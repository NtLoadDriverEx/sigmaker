#![feature(slice_take)]
#![feature(new_uninit)]
#![feature(scoped_threads)]

#[macro_use]
extern crate lazy_static;

extern crate core;

extern crate crossbeam;

use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::{Deref, DerefMut};
use std::ptr::slice_from_raw_parts;
use std::sync::Mutex;
use std::{mem, slice, vec};

use crossbeam::thread;

use crate::SigPart::Wildcard;
use binaryninja::architecture::{Architecture, CoreArchitecture};
use binaryninja::backgroundtask::BackgroundTask;
use binaryninja::command::{register_for_address, register_for_function, register_for_range};
use binaryninja::function::Function;
use binaryninja::llil::{Finalized, InstrInfo, NonSSA, RegularNonSSA};
use binaryninja::rc::{Guard, Ref};
use binaryninja::{
    binaryninjacore_sys::*,
    binaryview::{BinaryView, BinaryViewExt},
    command::register,
    disassembly::{DisassemblyTextLine, InstructionTextToken, InstructionTextTokenType},
    platform::Platform,
};
use iced_x86::Register::{RBP, RSP};
use iced_x86::{
    Decoder, DecoderOptions, Formatter, Instruction, InstructionInfoFactory, Mnemonic,
    NasmFormatter, OpKind, Register, UsedRegister,
};
use log::{error, info, log};

fn get_constants_by_ref(func: &Function, addr: u64) -> Option<&[BNConstantReference]> {
    let mut size: usize = 0;

    let result = unsafe {
        BNGetConstantsReferencedByInstruction(func.handle, func.arch().0, addr, &mut size as *mut _)
    };

    if result.is_null() {
        return None;
    }

    unsafe {
        Some(slice::from_raw_parts_mut(
            result as *mut BNConstantReference,
            size,
        ))
    }
}

#[derive(Clone)]
enum SigPart {
    Byte(u8),
    Wildcard,
}

struct Creator {
    pub(crate) task: Ref<BackgroundTask>,
    pub(crate) view: Ref<BinaryView>,
    pub(crate) func: Ref<Function>,
}

impl Creator {
    fn new(
        view_handle: *mut BNBinaryView,
        func_handle: *mut BNFunction,
    ) -> Result<Self, &'static str> {
        return if let Ok(task) = BackgroundTask::new("Creating signature... :)", true) {
            Ok(Self {
                task,
                view: unsafe { BinaryView::from_raw(view_handle) },
                func: unsafe { Function::from_raw(func_handle) },
            })
        } else {
            Err("Failed to create background task.")
        };
    }

    fn run(&self) {
        make_signature_task(self.view.as_ref(), self.func.as_ref(), &self.task)
    }
}

fn test_signature(func: Guard<Function>, sig: &[SigPart]) -> bool {
    let function_size = get_function_size(&func);
    let function_bytes = func.view().read_vec(func.start(), function_size);

    for i in 0..sig.len() {
        match sig.get(i).unwrap() {
            SigPart::Wildcard => continue,
            SigPart::Byte(opcode) => {
                if function_bytes.get(i).unwrap() != opcode {
                    return false;
                }
            }
        }
    }
    true
}

fn analyze_instructions(start: u64, func: &[u8]) -> Option<(Vec<SigPart>, Vec<u64>)> {
    let mut info_factory = InstructionInfoFactory::new();
    let mut decoder = Decoder::with_ip(64, func, start, DecoderOptions::NONE);

    let mut instruction = Instruction::default();
    let mut sig: Vec<SigPart> = Vec::new();
    let mut instruction_idxs: Vec<u64> = Vec::new();

    func.iter()
        .for_each(|x| sig.push(SigPart::Byte(x.clone())));

    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);
        let offsets = decoder.get_constant_offsets(&instruction);

        let idx: usize = (instruction.ip() - start) as usize;
        instruction_idxs.push(idx as u64);

        if offsets.has_displacement() {
            info!(
                "Rip Relative Instruction: {:016X} {}",
                instruction.ip(),
                instruction
            );

            let begin = idx + offsets.displacement_offset();
            let end = begin + offsets.displacement_size();

            for i in begin..=end {
                if let Some(byte) = sig.get_mut(i) {
                    *byte = Wildcard;
                } else {
                    return None;
                }
            }
        }

        if offsets.has_immediate() {
            let info = info_factory.info(&instruction);

            for register in info.used_registers() {
                if register.register() == RSP {
                    continue;
                };
                if register.register() == RBP {
                    continue;
                };
            }

            let begin = idx + offsets.immediate_offset();
            let end = begin + offsets.immediate_size();

            match instruction.mnemonic() {
                Mnemonic::Cmp => {}
                Mnemonic::Sub => {}
                _ => {
                    info!(
                        "Relative Instruction: {:016X} {}",
                        instruction.ip(),
                        instruction
                    );
                    for i in begin..=end {
                        if let Some(byte) = sig.get_mut(i) {
                            *byte = Wildcard;
                        } else {
                            return None;
                        }
                    }
                }
            }
        }
    }

    Option::from((sig, instruction_idxs))
}

fn log_signature(title: &str, sig: &Vec<SigPart>) {
    let mut sig_fmt = format!("{}", title);
    sig.iter().for_each(|opcode| match opcode {
        SigPart::Byte(code) => sig_fmt += &format!("{:02x} ", code),
        Wildcard => sig_fmt += &format!("? "),
    });

    info!("{}", sig_fmt.as_str());
}

fn make_signature_task(view: &BinaryView, func: &Function, task: &Ref<BackgroundTask>) {
    let funcs = view.functions();

    let is_unique = |sig: &[SigPart]| -> bool {
        let mut matches = 0;
        let mut index = 0;
        for func in &funcs {
            index += 1;
            task.set_progress_text(format!("Checking functions {}/{}", index, funcs.len()));
            if test_signature(func, sig) {
                matches += 1;
            }
        }

        !(matches > 1)
    };

    let function_size = get_function_size(func);

    let function_bytes = func.view().read_vec(func.start(), function_size);

    if let Some((sig, instruction_idxs)) =
        analyze_instructions(func.start(), function_bytes.as_slice())
    {
        log_signature("Initial Sig: ", &sig);
        if !is_unique(sig.as_slice()) {
            info!("Function too short to be unique");
            task.finish();
            return;
        }
        let len = instruction_idxs.len();
        for idx in instruction_idxs {
            task.set_progress_text(format!("Optimizing Signature {}/{}", idx, len));

            if task.is_cancelled() {
                task.finish();
                break;
            }

            let mut test_sig = sig.clone();
            let _ = test_sig.split_off(idx as usize);
            if !is_unique(test_sig.as_slice()) {
                continue;
            } else {
                log_signature("Optimal Sig: ", &test_sig);
                task.finish();
                break;
            }
        }
        info!("Complete.");
    } else {
        error!("analyze_instructions failed on func {}.", func.start());
        task.finish();
    }
}

fn create_signature(view: &BinaryView, func: &Function) {
    unsafe {
        lazy_static! {
            static ref TASK: Mutex<Option<Creator>> = Mutex::new(None);
        }

        *TASK.lock().unwrap() = Option::from(Creator::new(view.handle, func.handle).unwrap());

        std::thread::spawn(move || TASK.lock().unwrap().as_ref().unwrap().run());
    };
}

fn get_function_size(func: &Function) -> usize {
    let blocks = func.basic_blocks();
    let mut function_size: usize = 0;
    blocks
        .iter()
        .for_each(|block| function_size += block.raw_length() as usize);
    function_size
}

#[no_mangle]
pub extern "C" fn UIPluginInit() -> bool {
    binaryninja::logger::init(log::LevelFilter::Info).expect("Failed to init logger.");
    register_for_function(
        "Create Signature",
        "Automatically creats a signature for the selected function",
        create_signature,
    );

    //register_for_range()
    // register_for_address(
    //     "Create Signature",
    //     "Automatically creats an array of byte signature for the selected address.",
    //     create_signature,
    // );
    true
}
