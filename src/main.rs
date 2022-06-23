use std::{fmt, ops::Shl};

const NOP: u8 = 0xea;

struct Mos6502 {
    addr: u16,
    mem: [u8; u16::MAX as usize + 1],
    current_instruction: Option<u8>,
}

impl Mos6502 {
    fn new(mem: [u8; u16::MAX as usize + 1]) -> Self {
        let mut cpu = Self {
            mem,
            addr: 0,
            current_instruction: None,
        };
        cpu.reset();
        cpu
    }

    fn reset(&mut self) {
        // During reset sequence 6502 loads in the 16b addr (little endian) at 0xfffc
        self.addr = (self.mem[0xfffd] as u16).shl(8) + self.mem[0xfffc] as u16;
    }

    fn cycle(&mut self) {
        match self.current_instruction {
            Some(NOP) => {
                // NOP takes 2 clock cycles
                self.current_instruction = None;
                self.addr += 1;
            }
            Some(code) => todo!("Implement handling of {}", code),
            None => match self.mem[self.addr as usize] {
                NOP => self.current_instruction = Some(NOP),
                code => panic!("Instruction {} not handled", code),
            },
        }
    }
}

impl fmt::Debug for Mos6502 {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{0:#06x} {1:#04X} | {0:#018b} {1:#010b}",
            self.addr, self.mem[self.addr as usize]
        )
    }
}

fn main() {
    // Fill ROM with NOPs
    let rom = [NOP; u16::MAX as usize + 1];
    let mut cpu = Mos6502::new(rom);

    // CPU should start executing at 0xeaea and do NOP forever
    // Increasing the value on the addr bus every 2 cycles
    loop {
        println!("{:?}", cpu);
        cpu.cycle()
    }
}
