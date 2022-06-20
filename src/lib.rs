#[macro_use]
extern crate lazy_static;

use std::sync::Mutex;

use binaryninja::{
    binaryview::{BinaryView, BinaryViewExt},
    backgroundtask::BackgroundTask,
    command::{register_for_function},
    function::Function,
    rc::{Guard, Ref}
};

use iced_x86::{
    Decoder,
    DecoderOptions,
    Instruction,
    InstructionInfoFactory,
    Mnemonic,
    Register::{RBP, RSP}
};

use log::{error, info};

#[derive(Clone)]
enum SigPart {
    Byte(u8),
    Wildcard,
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
    let mut instruction_indices: Vec<u64> = Vec::new();

    func.iter()
        .for_each(|x| sig.push(SigPart::Byte(x.clone())));

    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);
        let offsets = decoder.get_constant_offsets(&instruction);

        let idx: usize = (instruction.ip() - start) as usize;
        instruction_indices.push(idx as u64);

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
                    *byte = SigPart::Wildcard;
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
                            *byte = SigPart::Wildcard;
                        } else {
                            return None;
                        }
                    }
                }
            }
        }
    }

    Option::from((sig, instruction_indices))
}

fn log_signature(title: &str, sig: &Vec<SigPart>) {
    info!("{}", title);
    let mut sig_fmt = String::new();
    sig.iter().for_each(|opcode| match opcode {
        SigPart::Byte(code) => sig_fmt += &format!("{:02x} ", code),
        SigPart::Wildcard => sig_fmt += &format!("? "),
    });

    info!("{}", sig_fmt.as_str());
}

fn get_function_size(func: &Function) -> usize {
    let blocks = func.basic_blocks();
    let mut function_size: usize = 0;
    blocks
        .iter()
        .for_each(|block| function_size += block.raw_length() as usize);
    function_size
}

struct CreateSignatureTask {
    pub(crate) task: Ref<BackgroundTask>,
    pub(crate) view: Ref<BinaryView>,
    pub(crate) func: Ref<Function>,
}

impl CreateSignatureTask {
    fn new(
        view: Ref<BinaryView>,
        func: Ref<Function>,
    ) -> Result<Self, &'static str> {
        return if let Ok(task) = BackgroundTask::new("Creating signature... :)", true) {
            Ok(Self { task, view, func, })
        } else {
            Err("Failed to create background task.")
        };
    }

    fn signature_task(&self) {
        let funcs = self.view.functions();

        let is_unique = |sig: &[SigPart]| -> bool {
            let mut matches = 0;

            for func in &funcs {
                if test_signature(func, sig) {
                    matches += 1;
                }
            }

            !(matches > 1)
        };

        let function_size = get_function_size(&self.func);

        let function_bytes = self.func.view().read_vec(self.func.start(), function_size);

        if let Some((sig, indices)) =
        analyze_instructions(self.func.start(), function_bytes.as_slice())
        {
            log_signature("Initial Sig: ", &sig);
            if !is_unique(sig.as_slice()) {
                info!("Function too short to be unique");
                self.task.finish();
                return;
            }
            let len = indices.len();
            for idx in indices {
                self.task.set_progress_text(format!("Optimizing Signature {}/{}", idx, len));

                if self.task.is_cancelled() {
                    self.task.finish();
                    break;
                }

                let mut test_sig = sig.clone();
                let _ = test_sig.split_off(idx as usize);
                if !is_unique(test_sig.as_slice()) {
                    continue;
                } else {
                    log_signature("Optimal Sig: ", &test_sig);
                    self.task.finish();
                    break;
                }
            }
            info!("Complete.");
        } else {
            error!("analyze_instructions failed on func {}.", self.func.start());
            self.task.finish();
        }
    }

}

fn create_signature(view: &BinaryView, func: &Function) {
    // Hacky solution to get around view and func lifetimes - im new to rust
    // there has to be a better way than this -_-
    lazy_static! {
        static ref TASK: Mutex<Option<CreateSignatureTask >> = Mutex::new(None);
    }

    *TASK.lock().unwrap() = Option::from(
        CreateSignatureTask::new(
            view.to_owned(),
            func.to_owned()).unwrap()
    );

    std::thread::spawn(|| TASK.lock().unwrap().as_ref().unwrap().signature_task());
}

#[no_mangle]
pub extern "C" fn UIPluginInit() -> bool {
    binaryninja::logger::init(log::LevelFilter::Info).expect("Failed to init logger.");
    register_for_function(
        "Create Signature",
        "Automatically creates a signature for the selected function",
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
