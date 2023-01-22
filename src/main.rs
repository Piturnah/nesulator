// TODO
// - Refactor out SR::N and SR::Z checks

use std::{fmt, ops::Shl};

use m6502::{opcodes::*, SR};

use crossterm::{style::Attribute, terminal::ClearType};

mod parse;

const SIGN: u8 = 0x80;

#[derive(Debug, Copy, Clone)]
#[allow(clippy::upper_case_acronyms)]
enum Op {
    ADC(AddrMode), // add with carry
    AND(AddrMode), // and (with accumulator)
    ASL(AddrMode), // arithmetic shift left
    BCC(AddrMode), // branch on carry clear
    BCS(AddrMode), // branch on carry set
    BEQ(AddrMode), // branch on equal (zero set)
    BIT(AddrMode), // bit test
    BMI(AddrMode), // branch on minus (negative set)
    BNE(AddrMode), // branch on not equal (zero clear)
    BPL(AddrMode), // branch on plus (negative clear)
    BRK(AddrMode), // break / interrupt
    BVC(AddrMode), // branch on overflow clear
    BVS(AddrMode), // branch on overflow set
    CLC(AddrMode), // clear carry
    CLD(AddrMode), // clear decimal
    CLI(AddrMode), // clear interrupt disable
    CLV(AddrMode), // clear overflow
    CMP(AddrMode), // compare (with accumulator)
    CPX(AddrMode), // compare with X
    CPY(AddrMode), // compare with Y
    DEC(AddrMode), // decrement
    DEX(AddrMode), // decrement X
    DEY(AddrMode), // decrement Y
    EOR(AddrMode), // exclusive or (with accumulator)
    INC(AddrMode), // increment
    INX(AddrMode), // increment X
    INY(AddrMode), // increment Y
    JMP(AddrMode), // jump
    JSR(AddrMode), // jump subroutine
    LDA(AddrMode), // load accumulator
    LDX(AddrMode), // load X
    LDY(AddrMode), // load Y
    LSR(AddrMode), // logical shift right
    NOP,           // no operation
    ORA(AddrMode), // or with accumulator
    PHA(AddrMode), // push accumulator
    PHP(AddrMode), // push processor status (SR)
    PLA(AddrMode), // pull accumulator
    PLP(AddrMode), // pull processor status (SR)
    ROL(AddrMode), // rotate left
    ROR(AddrMode), // rotate right
    RTI(AddrMode), // return from interrupt
    RTS(AddrMode), // return from subroutine
    SBC(AddrMode), // subtract with carry
    SEC(AddrMode), // set carry
    SED(AddrMode), // set decimal
    SEI(AddrMode), // set interrupt disable
    STA(AddrMode), // store accumulator
    STX(AddrMode), // store X
    STY(AddrMode), // store Y
    TAX(AddrMode), // transfer accumulator to X
    TAY(AddrMode), // transfer accumulator to Y
    TSX(AddrMode), // transfer stack pointer to X
    TXA(AddrMode), // transfer X to accumulator
    TXS(AddrMode), // transfer X to stack pointer
    TYA(AddrMode), // transfer Y to accumulator
}

#[derive(Debug, Copy, Clone)]
enum AddrMode {
    Accumulator,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Immediate,
    Implied,
    Indirect,
    XIndirect,
    IndirectY,
    Relative,
    Zeropage,
    ZeropageX,
    ZeropageY,
}

struct Mos6502 {
    pc: u16, // Program counter
    ra: u8,  // Accumulator
    rx: u8,  // Index register X
    ry: u8,  // Index register Y
    sp: u16, // Stack pointer
    sr: u8,  // Status register

    mem: [u8; u16::MAX as usize + 1], // Note: The stack is hardcoded to be between 0x0100 and 0x01ff
    current_instruction: Option<(Op, usize)>, // Option<(opcode, cycles left)>
                                      //         (_, 1) indicates it is the last clock cycle for the instruction
}

impl Mos6502 {
    // Initialise 6502 with provided memory and reset the address bus
    fn new(mem: [u8; u16::MAX as usize + 1]) -> Self {
        let mut cpu = Self {
            mem,
            pc: 0x0000,
            current_instruction: None,
            ra: 0x00,
            rx: 0x00,
            ry: 0x00,
            sp: 0x0100,
            sr: 0x00,
        };
        cpu.reset();
        cpu
    }

    fn reset(&mut self) {
        // During reset sequence 6502 loads in the 16b addr (little endian) at 0xfffc
        self.pc = (self.mem[0xfffd] as u16).shl(8) + self.mem[0xfffc] as u16;

        self.ra = 0;
        self.rx = 0;
        self.ry = 0;
        self.sr = 0;
    }

    // Add lhs and rhs, enable SR carry bit if there is carry
    //                         SR overflow bit if overflow
    fn add_with_carry(&mut self, lhs: u8, rhs: u8) -> u8 {
        let rhs = rhs.wrapping_add(match self.sr & SR::C {
            SR::C => 1,
            _ => 0,
        });

        let res = match lhs.checked_add(rhs) {
            Some(val) => {
                self.sr &= !SR::C;
                val
            }
            None => {
                self.sr |= SR::C;
                lhs.wrapping_add(rhs)
            }
        };

        let carry_out_6 = (lhs << 1).checked_add(rhs << 1).is_none();
        self.sr |= match carry_out_6 ^ (self.sr & SR::C > 0) {
            true => SR::V,
            false => 0,
        };

        res
    }

    fn get_operand_addr(&self, addr_mode: AddrMode) -> u16 {
        match addr_mode {
            AddrMode::Immediate => self.pc,
            AddrMode::Zeropage => self.mem[self.pc as usize] as u16,
            AddrMode::ZeropageX => self.mem[self.pc as usize].wrapping_add(self.rx) as u16,
            AddrMode::Absolute => {
                // lobyte
                let fetch_addr: u16 = self.mem[self.pc as usize] as u16;
                // hibyte
                fetch_addr + (self.mem[self.pc as usize + 1] as u16).shl(8)
            }
            AddrMode::AbsoluteX => {
                // lobyte
                let fetch_addr: u16 = (self.mem[self.pc as usize] as u16) + self.rx as u16;
                // hibyte
                fetch_addr + (self.mem[self.pc as usize + 1] as u16).shl(8)
            }
            AddrMode::AbsoluteY => {
                // lobyte
                let fetch_addr: u16 = (self.mem[self.pc as usize] as u16) + self.ry as u16;
                // hibyte
                fetch_addr + (self.mem[self.pc as usize + 1] as u16).shl(8)
            }
            AddrMode::XIndirect => {
                // NOTE: potential carry bugs here to investigate if things become weird
                let addr = self.mem[self.pc as usize].wrapping_add(self.rx) as usize;
                (self.mem[addr + 1] as u16).shl(8) + self.mem[addr] as u16
            }
            AddrMode::IndirectY => {
                let ind_addr = self.mem[self.pc as usize] as usize;
                (self.mem[ind_addr + 1] as u16).shl(8) + self.mem[ind_addr] as u16 + self.ry as u16
            }
            _ => todo!("handling of `get_operand_addr` for {:?}", addr_mode),
        }
    }

    fn get_operand(&mut self, addr_mode: AddrMode) -> u8 {
        match addr_mode {
            AddrMode::AbsoluteX => {
                // Lobyte
                let (mut addr, carry) = match self.mem[self.pc as usize].checked_add(self.rx) {
                    Some(val) => {
                        self.current_instruction = None;
                        (val as usize, false)
                    }
                    None => {
                        self.current_instruction = Some((Op::NOP, 1));
                        (
                            self.mem[self.pc as usize].wrapping_add(self.rx) as usize,
                            true,
                        )
                    }
                };
                // Hibyte
                // Inc page on carry
                addr += (self.mem[self.pc as usize + 1] as usize
                    + match carry {
                        true => 1,
                        false => 0,
                    })
                    << 8;

                self.mem[addr]
            }
            AddrMode::AbsoluteY => {
                // Lobyte
                let (mut addr, carry) = match self.mem[self.pc as usize].checked_add(self.ry) {
                    Some(val) => {
                        self.current_instruction = None;
                        (val as usize, false)
                    }
                    None => {
                        self.current_instruction = Some((Op::NOP, 1));
                        (
                            self.mem[self.pc as usize].wrapping_add(self.ry) as usize,
                            true,
                        )
                    }
                };
                // Hibyte
                // Inc page on carry
                addr += (self.mem[self.pc as usize + 1] as usize
                    + match carry {
                        true => 1,
                        false => 0,
                    })
                    << 8;
                self.mem[addr]
            }
            _ => self.mem[self.get_operand_addr(addr_mode) as usize],
        }
    }

    fn cycle(&mut self) {
        if self.current_instruction.is_none() {
            use AddrMode::*;
            self.current_instruction = Some(match self.mem[self.pc as usize] {
                NOP => (Op::NOP, 2),
                ADC::IMM => (Op::ADC(Immediate), 2),
                ADC::ZPG => (Op::ADC(Zeropage), 3),
                ADC::ZPG_X => (Op::ADC(ZeropageX), 4),
                ADC::ABS => (Op::ADC(Absolute), 4),
                ADC::ABS_X => (Op::ADC(AbsoluteX), 4),
                ADC::ABS_Y => (Op::ADC(AbsoluteY), 4),
                ADC::X_IND => (Op::ADC(XIndirect), 6),
                ADC::IND_Y => (Op::ADC(IndirectY), 5),
                SBC_IMM => (Op::SBC(Immediate), 2),
                SBC_ZPG => (Op::SBC(Zeropage), 3),
                AND::IMM => (Op::AND(Immediate), 2),
                AND::ZPG => (Op::AND(Zeropage), 3),
                AND::ZPG_X => (Op::AND(ZeropageX), 4),
                AND::ABS => (Op::AND(Absolute), 4),
                AND::ABS_X => (Op::AND(AbsoluteX), 4),
                AND::ABS_Y => (Op::AND(AbsoluteY), 4),
                AND::X_IND => (Op::AND(XIndirect), 6),
                AND::IND_Y => (Op::AND(IndirectY), 5),
                ASL::ACC => (Op::ASL(Accumulator), 2),
                ASL::ZPG => (Op::ASL(Zeropage), 5),
                ASL::ZPG_X => (Op::ASL(ZeropageX), 6),
                ASL::ABS => (Op::ASL(Absolute), 6),
                ASL::ABS_X => (Op::ASL(AbsoluteX), 7),
                BNE => (Op::BNE(Implied), 2),
                CMP::IMM => (Op::CMP(Immediate), 2),
                CMP::ZPG => (Op::CMP(Zeropage), 3),
                CMP::ZPG_X => (Op::CMP(ZeropageX), 4),
                CMP::ABS => (Op::CMP(Absolute), 4),
                CMP::ABS_X => (Op::CMP(AbsoluteX), 4),
                CMP::ABS_Y => (Op::CMP(AbsoluteY), 4),
                CMP::X_IND => (Op::CMP(XIndirect), 6),
                CMP::IND_Y => (Op::CMP(IndirectY), 5),
                LDA::IMM => (Op::LDA(Immediate), 2),
                LDA::ZPG => (Op::LDA(Zeropage), 3),
                PHA => (Op::PHA(Implied), 3),
                PLA => (Op::PLA(Implied), 4),
                STA::ZPG => (Op::STA(Zeropage), 3),
                CLC => (Op::CLC(Implied), 2),
                SEC => (Op::SEC(Implied), 2),
                code => panic!("Opcode {code:#04x} currently not supported"),
            });
            self.pc += 1;
        };

        match self.current_instruction.unwrap() {
            (op, 1) => {
                // Last clock cycle for instruction
                match op {
                    Op::NOP => self.current_instruction = None,
                    Op::ADC(addr_mode) => {
                        let operand = self.get_operand(addr_mode);
                        self.ra = self.add_with_carry(self.ra, operand);
                        match addr_mode {
                            AddrMode::AbsoluteX | AddrMode::AbsoluteY => self.pc += 2,
                            _ => {
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                        }

                        if self.ra & SIGN > 0 {
                            self.sr |= SR::N;
                        } else {
                            self.sr &= !SR::N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR::Z;
                        } else {
                            self.sr &= !SR::Z;
                        }
                    }
                    Op::AND(addr_mode) => {
                        let operand = self.get_operand(addr_mode);
                        self.ra &= operand;
                        match addr_mode {
                            AddrMode::AbsoluteX | AddrMode::AbsoluteY => self.pc += 2,
                            _ => {
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                        }

                        if self.ra & SIGN > 0 {
                            self.sr |= SR::N;
                        } else {
                            self.sr &= !SR::N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR::Z;
                        } else {
                            self.sr &= !SR::Z;
                        }
                    }
                    Op::ASL(addr_mode) => match addr_mode {
                        AddrMode::Accumulator => {
                            match self.ra >> 7 == 1 {
                                true => self.sr |= SR::C,
                                false => self.sr &= !SR::C,
                            }

                            self.ra = self.ra << 1;

                            if self.ra & SIGN > 0 {
                                self.sr |= SR::N;
                            } else {
                                self.sr &= !SR::N;
                            }
                            if self.ra == 0 {
                                self.sr |= SR::Z;
                            } else {
                                self.sr &= !SR::Z;
                            }
                        }
                        addr_mode => {
                            let addr = self.get_operand_addr(addr_mode);
                            let operand = self.mem[addr as usize];

                            match operand >> 7 == 1 {
                                true => self.sr |= SR::C,
                                false => self.sr &= !SR::C,
                            }

                            self.mem[addr as usize] = operand << 1;
                            let operand = self.mem[addr as usize];

                            if operand & SIGN > 0 {
                                self.sr |= SR::N;
                            } else {
                                self.sr &= !SR::N;
                            }
                            if operand == 0 {
                                self.sr |= SR::Z;
                            } else {
                                self.sr &= !SR::Z;
                            }
                        }
                    },
                    Op::CMP(addr_mode) => {
                        let operand = (!self.get_operand(addr_mode)).wrapping_add(1);
                        let res = match self.ra.checked_add(operand) {
                            Some(val) => {
                                self.sr &= !SR::C;
                                val
                            }
                            None => {
                                self.sr |= SR::C;
                                self.ra.wrapping_add(operand)
                            }
                        };
                        match addr_mode {
                            AddrMode::AbsoluteX | AddrMode::AbsoluteY => self.pc += 2,
                            _ => {
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                        }
                        if res & SIGN > 0 {
                            self.sr |= SR::N;
                        } else {
                            self.sr &= !SR::N;
                        }
                        if res == 0 {
                            self.sr |= SR::Z;
                        } else {
                            self.sr &= !SR::Z;
                        }
                    }
                    Op::LDA(addr_mode) => {
                        let operand = self.get_operand(addr_mode);
                        self.ra = operand;
                        match addr_mode {
                            AddrMode::AbsoluteX | AddrMode::AbsoluteY => self.pc += 2,
                            _ => {
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                        }
                        if self.ra & SIGN > 0 {
                            self.sr |= SR::N;
                        } else {
                            self.sr &= !SR::N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR::Z;
                        } else {
                            self.sr &= !SR::Z;
                        }
                    }
                    // TODO: Tests
                    Op::PHA(_) => {
                        self.mem[self.sp as usize] = self.ra;
                        self.dec_sp();
                        self.current_instruction = None;
                    }
                    // TODO: Tests & SR
                    Op::PLA(_) => {
                        self.inc_sp();
                        self.ra = self.mem[self.sp as usize];
                        self.current_instruction = None;

                        if self.ra & SIGN > 0 {
                            self.sr |= SR::N;
                        } else {
                            self.sr &= !SR::N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR::Z;
                        } else {
                            self.sr &= !SR::Z;
                        }
                    }
                    // TODO: Tests
                    Op::STA(addr_mode) => {
                        match addr_mode {
                            AddrMode::Zeropage => {
                                self.mem[self.mem[self.pc as usize] as usize] = self.ra;
                                self.pc += 1;
                                self.current_instruction = None;
                            }
                            _ => todo!("handling of STA for {:?}", addr_mode),
                        }
                        if self.ra & SIGN > 0 {
                            self.sr |= SR::N;
                        } else {
                            self.sr &= !SR::N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR::Z;
                        }
                    }
                    // TODO: Tests
                    Op::SBC(addr_mode) => {
                        let operand = !self.get_operand(addr_mode);
                        self.ra = self.add_with_carry(self.ra, operand);
                        match addr_mode {
                            AddrMode::AbsoluteX | AddrMode::AbsoluteY => self.pc += 2,
                            _ => {
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                        }

                        if self.ra & SIGN > 0 {
                            self.sr |= SR::N;
                        } else {
                            self.sr &= !SR::N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR::Z;
                        }
                    }
                    Op::CLC(_) => {
                        self.sr &= !SR::C;
                        self.current_instruction = None;
                    }
                    Op::SEC(_) => {
                        self.sr |= SR::C;
                        self.current_instruction = None;
                    }
                    Op::BNE(_) => match self.sr & SR::Z {
                        SR::Z => {
                            self.pc += 1;
                            self.current_instruction = None;
                        }
                        _ => {
                            let current_op = self.pc - 1;
                            let offset = self.mem[self.pc as usize] as i8;
                            // NOTE: we are currently offsetting from the BNE instruction, rather than the
                            //    operand. Unsure if this is correct. TODO investigate
                            self.pc = current_op.wrapping_add(offset as u16);
                            self.current_instruction = Some((
                                Op::NOP,
                                match self.pc >> 8 == current_op >> 8 {
                                    true => 1,
                                    false => 2,
                                },
                            ))
                        }
                    },
                    op => todo!("Implement handling for {op:?}"),
                }
            }

            (op, cycles) => self.current_instruction = Some((op, cycles - 1)),
        }
    }

    fn dec_sp(&mut self) {
        self.sp -= 1;
        if self.sp < 0x0100 {
            self.sp = 0x01ff;
        }
    }

    fn inc_sp(&mut self) {
        self.sp += 1;
        if self.sp > 0x01ff {
            self.sp = 0x0100;
        }
    }
}

impl fmt::Display for Mos6502 {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        const WIDTH: usize = 16;
        let mut lines: Vec<_> = self.mem.chunks(WIDTH).enumerate().collect();
        lines.dedup_by(|(_, a), (_, b)| a == b);

        let mut prev_line = 0;
        for (i, line) in lines.iter() {
            if *i != 0 && prev_line != i - 1 {
                writeln!(f, " ...")?;
            }
            write!(f, "{:04x}: ", i * WIDTH)?;
            for (j, b) in line.iter().enumerate() {
                if j + i * WIDTH == self.pc as usize || j + i * WIDTH == self.sp as usize {
                    write!(f, "{}", Attribute::Reverse)?;
                }
                write!(f, "{:02x}{} ", b, Attribute::Reset)?;
            }
            write!(f, " ")?;
            for (j, b) in line.iter().enumerate() {
                if j + i * WIDTH == self.pc as usize || j + i * WIDTH == self.sp as usize {
                    write!(f, "{}", Attribute::Reverse)?;
                }
                write!(
                    f,
                    "{}",
                    match (*b as char).is_alphanumeric() {
                        true => *b as char,
                        false => '.',
                    }
                )?;
                write!(f, "{}", Attribute::Reset)?;
            }
            writeln!(f, "")?;
            prev_line = *i;
        }
        writeln!(f, "\n ACC: {0:#04x} ({0:03})", self.ra)?;
        write!(f, "  SR: {:#010b}", self.sr)
    }
}

impl fmt::Debug for Mos6502 {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{0:#06x} {1:#04x} | {0:#018b} {1:#010b}",
            self.pc, self.mem[self.pc as usize]
        )
    }
}

// This is for debugging or visualisation purposes
fn run_cartridge(rom: [u8; u16::MAX as usize + 1 - 0x4020]) {
    let mut mem = vec![0; u16::MAX as usize + 1];
    mem.splice(0x4020.., rom.iter().cloned());

    let mut cpu = Mos6502::new(mem.try_into().unwrap_or_else(|v: Vec<u8>| {
        panic!("Expected Vec of length {} but it was {}", 65536, v.len())
    }));

    loop {
        cpu.cycle();
        let buffer = format!("{}", cpu);
        println!("{}{}", crossterm::terminal::Clear(ClearType::All), buffer);
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}

fn main() {
    let mut args = std::env::args();
    args.next();
    if let Some(path) = args.next() {
        run_cartridge(
            std::fs::read(path)
                .unwrap()
                .try_into()
                .unwrap_or_else(|v: Vec<u8>| {
                    panic!(
                        "Please provide a binary of size {} bytes. Provided: {} bytes",
                        65536 - 0x4020,
                        v.len()
                    )
                }),
        )
    } else {
        println!("Please provide a ROM of size {} bytes", 65536 - 0x4020);
    }
}

#[cfg(test)]
mod test {
    use crate::*;

    // Fetch u16 from 16b address (little endian)
    fn fetch_u16(cpu: &Mos6502, addr: u16) -> u16 {
        let addr = addr as usize;
        cpu.mem[addr] as u16 + (cpu.mem[addr + 1] as u16).shl(8)
    }

    macro_rules! program {
	($($e:expr),*) => {{
	    let mut rom = vec![0; 0x4020];
	    rom.append(&mut vec![NOP; u16::MAX as usize + 1 - 0x4020]);
	    rom[0xfffc] = 0x20;
	    rom[0xfffd] = 0x40;

	    let program: Vec<u8> = vec![$($e),*];
	    rom.splice(0x4020..0x4020+program.len(), program.iter().cloned());
	    Mos6502::new(rom.try_into().unwrap_or_else(|v: Vec<u8>| {
		panic!(
                    "Expected Vec of length {} but it was {}",
                    65536 - 0x4020,
                    v.len()
		)
            }))
	}}
    }

    #[test]
    fn asl_abs_x() {
        let mut cpu = program![ASL::ABS_X, 0xff, 0x00];
        cpu.mem[0x0101] = 0b10010101;
        cpu.rx = 0x02;
        for _ in 0..7 {
            cpu.cycle();
        }
        assert_eq!(cpu.mem[0x0101], 0b00101010, "wrong value in mem");
        assert_eq!(cpu.sr, SR::C, "wrong SR flags");
    }

    #[test]
    fn asl_abs() {
        let mut cpu = program![ASL::ABS, 0x1f, 0x40];
        cpu.mem[0x401f] = 0b10010101;
        for _ in 0..6 {
            cpu.cycle();
        }
        assert_eq!(cpu.mem[0x401f], 0b00101010, "wrong value in mem");
        assert_eq!(cpu.sr, SR::C, "wrong SR flags");
    }

    #[test]
    fn asl_zpg_x() {
        let mut cpu = program![ASL::ZPG_X, 0xff];
        cpu.mem[0x01] = 0b10010101;
        cpu.rx = 0x02;
        for _ in 0..6 {
            cpu.cycle();
        }
        assert_eq!(cpu.mem[0x01], 0b00101010, "wrong value in mem");
        assert_eq!(cpu.sr, SR::C, "wrong SR flags");
    }

    #[test]
    fn asl_zpg() {
        let mut cpu = program![ASL::ZPG, 0x00];
        cpu.mem[0] = 0b10010101;
        for _ in 0..5 {
            cpu.cycle();
        }
        assert_eq!(cpu.mem[0], 0b00101010, "wrong value in mem");
        assert_eq!(cpu.sr, SR::C, "wrong SR flags");
    }

    #[test]
    fn asl_acc() {
        let mut cpu = program![LDA::IMM, 0b10010101, ASL::ACC];
        for _ in 0..4 {
            cpu.cycle();
        }
        assert_eq!(cpu.ra, 0b00101010, "wrong value in acc");
        assert_eq!(cpu.sr, SR::C, "wrong SR flags");
        let mut cpu = program![LDA::IMM, 0b00010101, ASL::ACC];
        for _ in 0..4 {
            cpu.cycle();
        }
        assert_eq!(cpu.ra, 0b00101010, "wrong value in acc");
        assert_eq!(cpu.sr, 0, "wrong SR flags");
    }

    #[test]
    fn bne_dont() {
        let mut cpu = program![LDA::IMM, 5, CMP::IMM, 5, BNE, 0x10, LDA::IMM, 0x42];
        for _ in 0..8 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn bne_do() {
        let mut cpu = program![LDA::IMM, 5, CMP::IMM, 23, BNE, 0x10];
        cpu.mem[0x4034] = LDA::IMM;
        cpu.mem[0x4035] = 0x42;
        for _ in 0..9 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn cmp_imm_lt() {
        let mut cpu = program![CMP::IMM, 5];
        cpu.ra = 6;
        for _ in 0..2 {
            cpu.cycle();
            println!("{}", cpu)
        }
        assert_eq!(cpu.sr, SR::C);
        assert_eq!(cpu.ra, 6); // ACC should not change
    }

    #[test]
    fn cmp_imm_gt() {
        let mut cpu = program![CMP::IMM, 5];
        cpu.ra = 4;
        for _ in 0..2 {
            cpu.cycle();
            println!("{}", cpu)
        }
        assert_eq!(cpu.sr, SR::N);
        assert_eq!(cpu.ra, 4); // ACC should not change
    }

    #[test]
    fn cmp_imm_eq() {
        let mut cpu = program![CMP::IMM, 5];
        cpu.ra = 5;
        for _ in 0..2 {
            cpu.cycle();
            println!("{}", cpu)
        }
        assert_eq!(cpu.sr, SR::Z | SR::C);
        assert_eq!(cpu.ra, 5); // ACC should not change
    }

    #[test]
    fn add_16bit() {
        let mut cpu = program![
            CLC,
            ADC::IMM,
            0xff,
            ADC::IMM,
            0x02,
            STA::ZPG,
            0x00,
            LDA::IMM,
            0x00,
            ADC::IMM,
            0x7f,
            STA::ZPG,
            0x01
        ];
        for _ in 0..16 {
            cpu.cycle();
            println!("{}", cpu)
        }
        assert_eq!(fetch_u16(&cpu, 0), 0x8001u16);
    }

    #[test]
    fn and_zpg() {
        let mut cpu = program![ADC::IMM, 0b01101100, AND::ZPG, 0x42];
        cpu.mem[0x0042] = 0b10101110;
        for _ in 0..5 {
            cpu.cycle();
            println!("{cpu}");
        }

        assert_eq!(cpu.ra, 0b00101100);
    }

    #[test]
    fn and_zpg_srz() {
        let mut cpu = program![ADC::ZPG, 0x02, AND::ZPG, 0x00];
        cpu.mem[0x0000] = 0x01;
        for _ in 0..5 {
            cpu.cycle()
        }

        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.sr, SR::Z);
    }

    // Alex suggested these test numbers
    #[test]
    fn adc_imm_alex() {
        let mut cpu = program![ADC::IMM, 0x06, AND::IMM, 84];
        for _ in 0..4 {
            cpu.cycle()
        }
        assert_eq!(cpu.ra, 0x04);
    }

    #[test]
    fn and_imm() {
        let mut cpu = program![ADC::IMM, 0x01, AND::IMM, 0x02];

        for _ in 0..2 {
            cpu.cycle()
        }
        assert_eq!(cpu.ra, 0x01);

        for _ in 0..2 {
            cpu.cycle()
        }
        assert_eq!(cpu.ra, 0x00);
    }

    #[test]
    fn adc_imm() {
        let mut cpu = program![ADC::IMM, 0x01];
        for _ in 0..2 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x01);
    }

    #[test]
    fn adc_imm_twice() {
        let mut cpu = program![ADC::IMM, 0x01, ADC::IMM, 0x01];
        for _ in 0..4 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x02);
    }

    #[test]
    fn adc_im_carry() {
        let mut cpu = program![ADC::IMM, 0x90];
        //Initialise accumulator
        cpu.ra = 0x80;

        for _ in 0..2 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x10);
        println!("Status register: {:#010b}", cpu.sr);
        assert_eq!(cpu.sr, SR::C | SR::V);
    }

    #[test]
    fn sbc_zpg() {
        let mut cpu = program![SEC, SBC_ZPG, 0x01];
        cpu.mem[0x0001] = 0x42;
        cpu.ra = 0x43;

        for _ in 0..5 {
            cpu.cycle();
            println!("{cpu}");
        }

        assert_eq!(cpu.ra, 0x01);
    }

    #[test]
    // Values from http://forum.6502.org/viewtopic.php?t=62
    fn sbc_sr() {
        let mut cpu = program![SEC, SBC_IMM, 0x0a];

        cpu.ra = 0xf8;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0xee);
        assert_eq!(cpu.sr, SR::N | SR::C);

        cpu.mem[0x4022] = 0x07;
        cpu.reset();
        cpu.ra = 0x81;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x7a);
        assert_eq!(cpu.sr, SR::V | SR::C);

        cpu.reset();
        cpu.ra = 0x7;
        cpu.mem[0x4022] = 0x2;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x5);
        assert_eq!(cpu.sr, SR::C);

        cpu.reset();
        cpu.ra = 0x7;
        cpu.mem[0x4022] = 0xfe;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x9);
        assert_eq!(cpu.sr, 0);

        cpu.reset();
        cpu.ra = 0x7;
        cpu.mem[0x4022] = 0x90;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x77);
        assert_eq!(cpu.sr, 0);

        cpu.reset();
        cpu.ra = 0x10;
        cpu.mem[0x4022] = 0x90;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x80);
        assert_eq!(cpu.sr, SR::N | SR::V);

        cpu.reset();
        cpu.ra = 0x10;
        cpu.mem[0x4022] = 0x91;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x7f);
        assert_eq!(cpu.sr, 0);
    }

    #[test]
    fn sbc_sr_neg_result() {
        let mut cpu = program![SEC, SBC_IMM, 0x09];
        cpu.ra = 0x7;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0xfe);
        assert_eq!(cpu.sr, SR::N);
    }

    #[test]
    fn adc_zpg() {
        let mut cpu = program![ADC::ZPG, 0x01];
        cpu.mem[0x0001] = 0x42;
        for _ in 0..3 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn adc_zpg_srz() {
        let mut cpu = program![ADC::ZPG, 0x00];
        cpu.mem[0x0000] = 0x00;
        for _ in 0..3 {
            cpu.cycle()
        }

        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.sr, SR::Z);
    }

    #[test]
    fn adc_zpg_twice() {
        let mut cpu = program![ADC::ZPG, 0x01, ADC::ZPG, 0x02];
        cpu.mem[0x0001] = 0x42;
        cpu.mem[0x0002] = 0x02;
        for _ in 0..6 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x44);
    }

    #[test]
    fn adc_zpg_x() {
        let mut cpu = program![ADC::ZPG_X, 0x01];
        cpu.mem[0x0006] = 0x42;
        cpu.rx = 0x05;

        for _ in 0..4 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn adc_abs() {
        let mut cpu = program![ADC::ABS, 0x06, 0x01];
        cpu.mem[0x0106] = 0x42;
        for _ in 0..4 {
            dbg!(&cpu);
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    // Determining that we've got the difference between C and V flags correct
    // These test cases are taken from `http://forum.6502.org/viewtopic.php?t=62`
    fn adc_srz_src() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        rom[0x4020] = ADC::IMM;
        rom[0x4021] = 0x07; // 7
        rom[0x4022] = ADC::IMM;
        rom[0x4023] = 0xfe; // -2

        let mut cpu = Mos6502::new(rom);

        for _ in 0..4 {
            dbg!(&cpu);
            cpu.cycle();
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x05);
        assert_eq!(cpu.sr, SR::C);

        cpu.mem[0x4023] = 0x02; // 7 + 2
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x09);
        assert_eq!(cpu.sr, 0);

        cpu.mem[0x4023] = 0x80; // 7 + 128
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x87);
        assert_eq!(cpu.sr, SR::N);

        cpu.mem[0x4023] = 0xf7; // 7 + -9
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0xfe);
        assert_eq!(cpu.sr, SR::N);

        cpu.mem[0x4023] = 0x7a; // 7 + 122
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x81);
        assert_eq!(cpu.sr, SR::N | SR::V);

        cpu.mem[0x4021] = 0x80; // 128
        cpu.mem[0x4023] = 0x90; // -16
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x10);
        assert_eq!(cpu.sr, SR::V | SR::C);

        cpu.mem[0x4021] = 0xf0; // -16
        cpu.mem[0x4023] = 0xf0; // -16
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0xe0); // -32
        assert_eq!(cpu.sr, SR::N | SR::C);

        cpu.mem[0x4021] = 0xf8; // -8
        cpu.mem[0x4023] = 0x0a; // 10
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x02);
        assert_eq!(cpu.sr, SR::C);
    }

    #[test]
    fn adc_abs_x() {
        let mut cpu = program![ADC::ABS_X, 0x10, 0x01];
        cpu.mem[0x0200] = 0x42;
        cpu.rx = 0xf0;

        for _ in 0..5 {
            cpu.cycle();
            println!("{cpu}")
        }

        assert_eq!(cpu.ra, 0x42);
        assert_eq!(cpu.sr, 0x00);
    }

    #[test]
    fn adc_abs_x_nocross() {
        let mut cpu = program![ADC::ABS_X, 0x10, 0x01];
        cpu.mem[0x0111] = 0x42;
        cpu.rx = 0x01;

        for _ in 0..4 {
            dbg!(&cpu);
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
        assert_eq!(cpu.sr, 0x00);
    }

    #[test]
    // Determine if AbsX takes correct number of cycles
    fn adc_abs_x_cycle() {
        // This should take 5 cycles as the RX offset is enough to cross the
        // page boundary
        let mut cpu = program![ADC::ABS_X, 0x10, 0x01, ADC::IMM, 0x01];
        cpu.mem[0x0200] = 0x01;
        cpu.rx = 0xf0;

        for _ in 0..6 {
            dbg!(&cpu);
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x01);
        cpu.cycle();
        assert_eq!(cpu.ra, 0x02);
    }

    #[test]
    fn adc_abs_y_nocross() {
        let mut cpu = program![ADC::ABS_Y, 0x10, 0x01];
        cpu.mem[0x0111] = 0x42;
        cpu.ry = 0x01;

        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}")
        }

        assert_eq!(cpu.ra, 0x42);
        assert_eq!(cpu.sr, 0x00);
    }

    #[test]
    // Determine if AbsX takes correct number of cycles
    fn adc_abs_y_cycle() {
        // This should take 5 cycles as the RX offset is enough to cross the
        // page boundary
        let mut cpu = program![ADC::ABS_Y, 0x10, 0x01, ADC::IMM, 0x01];
        cpu.mem[0x200] = 0x01;
        cpu.ry = 0xf0;

        for _ in 0..6 {
            dbg!(&cpu);
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x01);
        cpu.cycle();
        assert_eq!(cpu.ra, 0x02);
    }

    #[test]
    fn adc_x_indirect() {
        let mut cpu = program![ADC::X_IND, 0x20];
        cpu.mem[0x0024] = 0x74;
        cpu.mem[0x0025] = 0x20;
        cpu.mem[0x2074] = 0x42;
        cpu.rx = 0x04;

        for _ in 0..6 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn adc_indirect_y() {
        let mut cpu = program![ADC::IND_Y, 0x86];
        cpu.mem[0x0086] = 0x28;
        cpu.mem[0x0087] = 0x40;
        cpu.mem[0x4038] = 0x42;
        cpu.ry = 0x10;

        for _ in 0..5 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }
}
