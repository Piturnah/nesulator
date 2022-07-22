// References: https://www.masswerk.at/6502/6502_instruction_set.html

use std::{fmt, ops::Shl};

use crossterm::{style::Attribute, terminal::ClearType};

// Opcodes
const NOP: u8 = 0xea;
// Stack
const PHA: u8 = 0x48;
const PLA: u8 = 0x68;
// ADC
const ADC_IMM: u8 = 0x69;
const ADC_ZPG: u8 = 0x65;
const ADC_ZPG_X: u8 = 0x75;
const ADC_ABS: u8 = 0x6d;
const ADC_ABS_X: u8 = 0x7d;
const ADC_ABS_Y: u8 = 0x79;
const ADC_X_IND: u8 = 0x61;
const ADC_IND_Y: u8 = 0x71;
// SBC
const SBC_IMM: u8 = 0xe9;
const SBC_ZPG: u8 = 0xe5;
// AND
const AND_IMM: u8 = 0x29;
const AND_ZPG: u8 = 0x25;
// LDA
const LDA_IMM: u8 = 0xa9;
// STA
const STA_ZPG: u8 = 0x85;

const CLC: u8 = 0x18;
const SEC: u8 = 0x38;

// SR Flags
const SR_N: u8 = 0x80; // Negative
const SR_V: u8 = 0x40; // Overflow
const SR_B: u8 = 0x10; // Break*
const SR_D: u8 = 0x08; // Decimal
const SR_I: u8 = 0x04; // Interrupt
const SR_Z: u8 = 0x02; // Zero
const SR_C: u8 = 0x01; // Carry

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

    // Fetch u8 from 16b address (little endian)
    fn fetch(&self) -> u8 {
        // lobyte
        let mut fetch_addr: usize = self.mem[self.pc as usize] as usize;
        // hibyte
        fetch_addr += (self.mem[self.pc as usize + 1] as usize).shl(8);

        self.mem[fetch_addr]
    }

    // Fetch u16 from 16b address (little endian)
    fn fetch_u16(&self, addr: u16) -> u16 {
        let addr = addr as usize;
        self.mem[addr] as u16 + (self.mem[addr + 1] as u16).shl(8)
    }

    // Add lhs and rhs, enable SR carry bit if there is carry
    //                         SR overflow bit if overflow
    fn add_with_carry(&mut self, lhs: u8, rhs: u8) -> u8 {
        let rhs = rhs.wrapping_add(match dbg!(self.sr & SR_C) {
            SR_C => 1,
            _ => 0,
        });

        let res = match lhs.checked_add(rhs) {
            Some(val) => {
                self.sr &= !SR_C;
                val
            }
            None => {
                self.sr |= SR_C;
                lhs.wrapping_add(rhs)
            }
        };

        let carry_out_6 = (lhs << 1).checked_add(rhs << 1).is_none();
        self.sr |= match carry_out_6 ^ (self.sr & SR_C > 0) {
            true => SR_V,
            false => 0,
        };

        res
    }

    fn cycle(&mut self) {
        if self.current_instruction.is_none() {
            use AddrMode::*;
            self.current_instruction = Some(match self.mem[self.pc as usize] {
                NOP => (Op::NOP, 2),
                ADC_IMM => (Op::ADC(Immediate), 2),
                ADC_ZPG => (Op::ADC(Zeropage), 3),
                ADC_ZPG_X => (Op::ADC(ZeropageX), 4),
                ADC_ABS => (Op::ADC(Absolute), 4),
                ADC_ABS_X => (Op::ADC(AbsoluteX), 4),
                ADC_ABS_Y => (Op::ADC(AbsoluteY), 4),
                ADC_X_IND => (Op::ADC(XIndirect), 6),
                ADC_IND_Y => (Op::ADC(IndirectY), 5),
                SBC_IMM => (Op::SBC(Immediate), 2),
                SBC_ZPG => (Op::SBC(Zeropage), 3),
                AND_IMM => (Op::AND(Immediate), 2),
                LDA_IMM => (Op::LDA(Immediate), 2),
                PHA => (Op::PHA(Implied), 3),
                PLA => (Op::PLA(Implied), 4),
                STA_ZPG => (Op::STA(Zeropage), 3),
                CLC => (Op::CLC(Implied), 2),
                SEC => (Op::SEC(Implied), 2),
                code => panic!("Opcode {code:#04x} currently not supported"),
            });
            self.pc += 1;
        };

        match self.current_instruction.as_ref().unwrap() {
            (op, 1) => {
                // Last clock cycle for instruction
                match op {
                    Op::NOP => self.current_instruction = None,
                    Op::ADC(addr_mode) => {
                        match addr_mode {
                            AddrMode::Immediate => {
                                self.ra = self.add_with_carry(self.ra, self.mem[self.pc as usize]);

                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::Zeropage => {
                                self.ra = self.add_with_carry(
                                    self.ra,
                                    self.mem[self.mem[self.pc as usize] as usize],
                                );
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::ZeropageX => {
                                self.ra = self.add_with_carry(
                                    self.ra,
                                    self.mem[(self.mem[self.pc as usize] + self.rx) as usize],
                                );
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::Absolute => {
                                let operand = self.fetch();
                                self.ra = self.add_with_carry(self.ra, operand);
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            // TODO: Code duplication of AbsX and AbsY
                            AddrMode::AbsoluteX => {
                                // Lobyte
                                let mut addr: usize = self
                                    .add_with_carry(self.mem[self.pc as usize], self.rx)
                                    as usize;
                                // Hibyte
                                // The carry flag is in bit zero of SR, so to conditionally inc the page
                                // In the event that a carry occurred, we can just add (SR & C)
                                addr += ((self.mem[self.pc as usize + 1] + (self.sr & SR_C))
                                    as usize)
                                    .shl(8);

                                // Determine if additional cycle required
                                if self.sr & SR_C > 0 {
                                    self.current_instruction = Some((Op::NOP, 1));
                                } else {
                                    self.current_instruction = None;
                                }

                                // Clear carry bit
                                self.sr &= !SR_C;

                                self.ra = self.add_with_carry(self.ra, self.mem[addr]);
                                self.pc += 2;
                            }
                            AddrMode::AbsoluteY => {
                                // Lobyte
                                let mut addr: usize = self
                                    .add_with_carry(self.mem[self.pc as usize], self.ry)
                                    as usize;
                                // Hibyte
                                // The carry flag is in bit zero of SR, so to conditionally inc the page
                                // In the event that a carry occurred, we can just add (SR & C)
                                addr += ((self.mem[self.pc as usize + 1] + (self.sr & SR_C))
                                    as usize)
                                    .shl(8);

                                // Determine if additional cycle required
                                if self.sr & SR_C > 0 {
                                    self.current_instruction = Some((Op::NOP, 1));
                                } else {
                                    self.current_instruction = None;
                                }

                                // Clear carry bit
                                self.sr &= !SR_C;

                                self.ra = self.add_with_carry(self.ra, self.mem[addr]);
                                self.pc += 2;
                            }
                            AddrMode::XIndirect => {
                                let addr = (self.mem[self.pc as usize] + self.rx) as usize;
                                self.ra = self.add_with_carry(
                                    self.ra,
                                    self.mem[(self.mem[addr + 1] as usize).shl(8)
                                        + self.mem[addr] as usize],
                                );
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::IndirectY => {
                                let ind_addr = self.mem[self.pc as usize] as usize;

                                if self.mem[ind_addr].checked_add(self.ry).is_none() {
                                    self.current_instruction = Some((Op::NOP, 1));
                                } else {
                                    self.current_instruction = None;
                                }

                                self.ra = self.add_with_carry(
                                    self.ra,
                                    self.mem[(self.mem[ind_addr + 1] as usize).shl(8)
                                        + self.mem[ind_addr] as usize
                                        + self.ry as usize],
                                );
                                self.pc += 1;
                            }
                            addr_mode => todo!("Handling of ADC for {:?}", addr_mode),
                        }
                        // Check for an overflow
                        // if ra_sign == operand_sign && ra_sign != self.ra & SIGN {
                        //     self.sr |= SR_V;
                        // }
                        if self.ra & SIGN > 0 {
                            self.sr |= SR_N;
                        } else {
                            self.sr &= !SR_N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR_Z;
                        }
                    }
                    Op::AND(addr_mode) => match addr_mode {
                        AddrMode::Immediate => {
                            self.ra &= self.mem[self.pc as usize];
                            self.current_instruction = None;
                            self.pc += 1;
                        }
                        _ => todo!("Handling of AND for {:?}", addr_mode),
                    },
                    // TODO: Tests & SR
                    Op::LDA(addr_mode) => match addr_mode {
                        AddrMode::Immediate => {
                            self.ra = self.mem[self.pc as usize];
                            self.current_instruction = None;
                            self.pc += 1;
                        }
                        _ => todo!("handling of LDA for {:?}", addr_mode),
                    },
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
                    }
                    // TODO: Tests
                    Op::STA(addr_mode) => match addr_mode {
                        AddrMode::Zeropage => {
                            self.mem[self.mem[self.pc as usize] as usize] = self.ra;
                            self.pc += 1;
                            self.current_instruction = None;
                        }
                        _ => todo!("handling of STA for {:?}", addr_mode),
                    },
                    // TODO: Tests
                    Op::SBC(addr_mode) => {
                        // Cache signs
                        let ra_sign = self.ra & SIGN;
                        let operand_sign = self.mem[self.pc as usize] & SIGN;

                        match addr_mode {
                            AddrMode::Immediate => {
                                self.ra = self.add_with_carry(self.ra, !self.mem[self.pc as usize]);

                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::Zeropage => {
                                self.ra = self.add_with_carry(
                                    self.ra,
                                    !self.mem[self.mem[self.pc as usize] as usize],
                                );
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::ZeropageX => {
                                self.ra = self.add_with_carry(
                                    self.ra,
                                    !self.mem[(self.mem[self.pc as usize] + self.rx) as usize],
                                );
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::Absolute => {
                                let operand = self.fetch();
                                self.ra = self.add_with_carry(self.ra, !operand);
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            // TODO: Code duplication of AbsX and AbsY
                            AddrMode::AbsoluteX => {
                                // Lobyte
                                let mut addr: usize = self
                                    .add_with_carry(self.mem[self.pc as usize], self.rx)
                                    as usize;
                                // Hibyte
                                // The carry flag is in bit zero of SR, so to conditionally inc the page
                                // In the event that a carry occurred, we can just add (SR & C)
                                addr += ((self.mem[self.pc as usize + 1] + (self.sr & SR_C))
                                    as usize)
                                    .shl(8);

                                // Determine if additional cycle required
                                if self.sr & SR_C > 0 {
                                    self.current_instruction = Some((Op::NOP, 1));
                                } else {
                                    self.current_instruction = None;
                                }

                                // Clear carry bit
                                self.sr &= !SR_C;

                                self.ra = self.add_with_carry(self.ra, !self.mem[addr]);
                                self.pc += 2;
                            }
                            AddrMode::AbsoluteY => {
                                // Lobyte
                                let mut addr: usize = self
                                    .add_with_carry(self.mem[self.pc as usize], self.ry)
                                    as usize;
                                // Hibyte
                                // The carry flag is in bit zero of SR, so to conditionally inc the page
                                // In the event that a carry occurred, we can just add (SR & C)
                                addr += ((self.mem[self.pc as usize + 1] + (self.sr & SR_C))
                                    as usize)
                                    .shl(8);

                                // Determine if additional cycle required
                                if self.sr & SR_C > 0 {
                                    self.current_instruction = Some((Op::NOP, 1));
                                } else {
                                    self.current_instruction = None;
                                }

                                // Clear carry bit
                                self.sr &= !SR_C;

                                self.ra = self.add_with_carry(self.ra, !self.mem[addr]);
                                self.pc += 2;
                            }
                            AddrMode::XIndirect => {
                                let addr = (self.mem[self.pc as usize] + self.rx) as usize;
                                self.ra = self.add_with_carry(
                                    self.ra,
                                    !(self.mem[(self.mem[addr + 1] as usize).shl(8)
                                        + self.mem[addr] as usize]
                                        as u8),
                                );
                                self.current_instruction = None;
                                self.pc += 1;
                            }
                            AddrMode::IndirectY => {
                                let ind_addr = self.mem[self.pc as usize] as usize;

                                if self.mem[ind_addr].checked_add(self.ry).is_none() {
                                    self.current_instruction = Some((Op::NOP, 1));
                                } else {
                                    self.current_instruction = None;
                                }

                                self.ra = self.add_with_carry(
                                    self.ra,
                                    !(self.mem[(self.mem[ind_addr + 1] as usize).shl(8)
                                        + self.mem[ind_addr] as usize
                                        + self.ry as usize]
                                        as u8),
                                );
                                self.pc += 1;
                            }
                            addr_mode => todo!("Handling of SBC for {:?}", addr_mode),
                        }
                        // Check for an overflow
                        if ra_sign == operand_sign && ra_sign != self.ra & SIGN {
                            self.sr |= SR_V;
                        }
                        if self.ra & SIGN > 0 {
                            self.sr |= SR_N;
                        } else {
                            self.sr &= !SR_N;
                        }
                        if self.ra == 0 {
                            self.sr |= SR_Z;
                        }
                    }
                    Op::CLC(_) => {
                        self.sr &= !SR_C;
                        self.current_instruction = None;
                    }
                    Op::SEC(_) => {
                        self.sr |= SR_C;
                        self.current_instruction = None;
                    }
                    op => todo!("Implement handling for {op:?}"),
                }
            }

            (op, cycles) => self.current_instruction = Some((*op, cycles - 1)),
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
        writeln!(f, "\n ACC: {0:#04x} ({0})", self.ra)?;
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
        std::thread::sleep(std::time::Duration::from_millis(100));
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
                        "Please provide a binary of size {}. Provided: {}",
                        65536 - 0x4020,
                        v.len()
                    )
                }),
        )
    } else {
        println!("Please provide a ROM of size {}", 65536 - 0x4020);
    }
}

#[cfg(test)]
mod test {
    use crate::*;

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
    fn add_16bit() {
        let mut cpu = program![
            CLC, ADC_IMM, 0xff, ADC_IMM, 0x01, STA_ZPG, 0x00, LDA_IMM, 0x00, ADC_IMM, 0x7f,
            STA_ZPG, 0x01
        ];
        for _ in 0..16 {
            cpu.cycle();
            println!("{}", cpu)
        }
        assert_eq!(cpu.fetch_u16(0), 0x8001u16);
    }

    #[test]
    #[ignore]
    fn and_zpg() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0042] = 84;

        rom[0x4020] = ADC_IMM;
        rom[0x4021] = 0x01;
        rom[0x4022] = AND_ZPG; // 3 cycles
        rom[0x4023] = 0x42;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;
        let mut cpu = Mos6502::new(rom);

        for _ in 0..5 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x04);
    }

    #[test]
    #[ignore]
    fn and_zpg_srz() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0000] = 0x01;

        rom[0x4020] = ADC_ZPG;
        rom[0x4021] = 0x02;
        rom[0x4022] = AND_ZPG;
        rom[0x4023] = 0x00;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        for _ in 0..5 {
            cpu.cycle()
        }

        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.sr, SR_Z);
    }

    // Alex suggested these test numbers
    #[test]
    fn adc_imm_alex() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;
        rom[0x4020] = ADC_IMM; // 2 cycles
        rom[0x4021] = 0x06;
        rom[0x4022] = AND_IMM; // 2 cycles
        rom[0x4023] = 84;
        let mut cpu = Mos6502::new(rom);
        for _ in 0..4 {
            cpu.cycle()
        }
        assert_eq!(cpu.ra, 0x04);
    }

    #[test]
    fn and_imm() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;
        rom[0x4020] = ADC_IMM; // 2 cycles
        rom[0x4021] = 0x01;
        rom[0x4022] = AND_IMM; // 2 cycles
        rom[0x4023] = 0x02;
        let mut cpu = Mos6502::new(rom);

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
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0000] = ADC_IMM;
        rom[0x0001] = 0x01;
        rom[0xfffc] = 0x00;
        rom[0xfffd] = 0x00;
        let mut cpu = Mos6502::new(rom);

        for _ in 0..2 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x01);
    }

    #[test]
    fn adc_imm_twice() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0000] = ADC_IMM;
        rom[0x0001] = 0x01;
        rom[0x0002] = ADC_IMM;
        rom[0x0003] = 0x01;
        rom[0xfffc] = 0x00;
        rom[0xfffd] = 0x00;
        let mut cpu = Mos6502::new(rom);

        for _ in 0..4 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x02);
    }

    #[test]
    fn adc_im_carry() {
        let mut rom = [NOP; u16::MAX as usize + 1];

        // Program
        rom[0x4020] = ADC_IMM;
        rom[0x4021] = 0x90;

        // Reset vector
        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        //Initialise accumulator
        cpu.ra = 0x80;

        for _ in 0..2 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x10);
        println!("Status register: {:#010b}", cpu.sr);
        assert_eq!(cpu.sr, SR_C | SR_V);
    }

    #[test]
    fn sbc_zpg() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0001] = 0x42;

        rom[0x4020] = SEC;
        rom[0x4021] = SBC_ZPG;
        rom[0x4022] = 0x01;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
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
        let mut rom = [NOP; u16::MAX as usize + 1];

        rom[0x401f] = SEC;
        rom[0x4020] = SBC_IMM;
        rom[0x4021] = 0x0a;

        rom[0xfffc] = 0x1f;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);

        cpu.ra = 0xf8;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0xee);
        assert_eq!(cpu.sr, SR_N | SR_C);

        cpu.mem[0x4021] = 0x07;
        cpu.reset();
        cpu.ra = 0x81;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x7a);
        assert_eq!(cpu.sr, SR_V | SR_C);

        cpu.reset();
        cpu.ra = 0x7;
        cpu.mem[0x4021] = 0x2;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x5);
        assert_eq!(cpu.sr, SR_C);

        cpu.reset();
        cpu.ra = 0x7;
        cpu.mem[0x4021] = 0xfe;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x9);
        assert_eq!(cpu.sr, 0);

        cpu.reset();
        cpu.ra = 0x7;
        cpu.mem[0x4021] = 0x90;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x77);
        assert_eq!(cpu.sr, 0);

        cpu.reset();
        cpu.ra = 0x10;
        cpu.mem[0x4021] = 0x90;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x80);
        assert_eq!(cpu.sr, SR_N | SR_V);

        cpu.reset();
        cpu.ra = 0x10;
        cpu.mem[0x4021] = 0x91;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0x7f);
        assert_eq!(cpu.sr, 0);
    }

    #[test]
    #[ignore]
    fn sbc_sr_failing() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x4020] = SEC;
        rom[0x4021] = SBC_IMM;
        rom[0x4022] = 0x9;
        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;
        let mut cpu = Mos6502::new(rom);
        cpu.ra = 0x7;
        for _ in 0..4 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 0xfe);
        assert_eq!(cpu.sr, SR_N);
    }

    #[test]
    #[ignore]
    fn sbc_sr_failing_2() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x4020] = SEC;
        rom[0x4021] = SBC_IMM;
        rom[0x4022] = 0xfe;
        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;
        let mut cpu = Mos6502::new(rom);
        cpu.ra = 0xff;
        for _ in 0..2 {
            cpu.cycle();
            println!("{cpu}");
        }
        assert_eq!(cpu.ra, 1);
        assert_eq!(cpu.sr, SR_N);
    }

    #[test]
    fn adc_zpg() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0001] = 0x42;

        rom[0x4020] = ADC_ZPG;
        rom[0x4021] = 0x01;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;
        let mut cpu = Mos6502::new(rom);

        for _ in 0..3 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn adc_zpg_srz() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0000] = 0x00;

        rom[0x4020] = ADC_ZPG;
        rom[0x4021] = 0x00;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        for _ in 0..3 {
            cpu.cycle()
        }

        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.sr, SR_Z);
    }

    #[test]
    fn adc_zpg_twice() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0001] = 0x42;
        rom[0x0002] = 0x02;

        rom[0x4020] = ADC_ZPG;
        rom[0x4021] = 0x01;
        rom[0x4022] = ADC_ZPG;
        rom[0x4023] = 0x02;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;
        let mut cpu = Mos6502::new(rom);

        for _ in 0..6 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x44);
    }

    #[test]
    fn adc_zpg_x() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0006] = 0x42;

        rom[0x4020] = ADC_ZPG_X;
        rom[0x4021] = 0x01;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        cpu.rx = 0x05;

        for _ in 0..4 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn adc_abs() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0106] = 0x42;

        rom[0x4020] = ADC_ABS;
        rom[0x4021] = 0x06;
        rom[0x4022] = 0x01;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);

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

        rom[0x4020] = ADC_IMM;
        rom[0x4021] = 0x07; // 7
        rom[0x4022] = ADC_IMM;
        rom[0x4023] = 0xfe; // -2

        let mut cpu = Mos6502::new(rom);

        for _ in 0..4 {
            dbg!(&cpu);
            cpu.cycle();
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x05);
        assert_eq!(cpu.sr, SR_C);

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
        assert_eq!(cpu.sr, SR_N);

        cpu.mem[0x4023] = 0xf7; // 7 + -9
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0xfe);
        assert_eq!(cpu.sr, SR_N);

        cpu.mem[0x4023] = 0x7a; // 7 + 122
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x81);
        assert_eq!(cpu.sr, SR_N | SR_V);

        cpu.mem[0x4021] = 0x80; // 128
        cpu.mem[0x4023] = 0x90; // -16
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x10);
        assert_eq!(cpu.sr, SR_V | SR_C);

        cpu.mem[0x4021] = 0xf0; // -16
        cpu.mem[0x4023] = 0xf0; // -16
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0xe0); // -32
        assert_eq!(cpu.sr, SR_N | SR_C);

        cpu.mem[0x4021] = 0xf8; // -8
        cpu.mem[0x4023] = 0x0a; // 10
        cpu.reset();
        for _ in 0..4 {
            cpu.cycle()
        }
        println!("STATUS: {:#010b} | RA: {:#04x}", cpu.sr, cpu.ra);
        assert_eq!(cpu.ra, 0x02);
        assert_eq!(cpu.sr, SR_C);
    }

    #[test]
    fn adc_abs_x() {
        let mut rom = [NOP; u16::MAX as usize + 1];

        rom[0x4020] = ADC_ABS_X;
        rom[0x4021] = 0x10;
        rom[0x4022] = 0x01;

        rom[0x0200] = 0x42;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        cpu.rx = 0xf0;

        for _ in 0..5 {
            dbg!(&cpu);
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
        assert_eq!(cpu.sr, 0x00);
    }

    #[test]
    fn adc_abs_x_nocross() {
        let mut rom = [NOP; u16::MAX as usize + 1];

        rom[0x4020] = ADC_ABS_X;
        rom[0x4021] = 0x10;
        rom[0x4022] = 0x01;

        rom[0x0111] = 0x42;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
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
        let mut rom = [NOP; u16::MAX as usize + 1];

        rom[0x4020] = ADC_ABS_X; // This should take 5 cycles as the RX offset
        rom[0x4021] = 0x10; // Is enough to cross the page boundary
        rom[0x4022] = 0x01;
        rom[0x4023] = ADC_IMM;
        rom[0x4024] = 0x01;

        rom[0x0200] = 0x01;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
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
        let mut rom = [NOP; u16::MAX as usize + 1];

        rom[0x4020] = ADC_ABS_Y;
        rom[0x4021] = 0x10;
        rom[0x4022] = 0x01;

        rom[0x0111] = 0x42;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        cpu.ry = 0x01;

        for _ in 0..4 {
            dbg!(&cpu);
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
        assert_eq!(cpu.sr, 0x00);
    }

    #[test]
    // Determine if AbsX takes correct number of cycles
    fn adc_abs_y_cycle() {
        let mut rom = [NOP; u16::MAX as usize + 1];

        rom[0x4020] = ADC_ABS_Y; // This should take 5 cycles as the RX offset
        rom[0x4021] = 0x10; // Is enough to cross the page boundary
        rom[0x4022] = 0x01;
        rom[0x4023] = ADC_IMM;
        rom[0x4024] = 0x01;

        rom[0x0200] = 0x01;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
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
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0024] = 0x74;
        rom[0x0025] = 0x20;
        rom[0x2074] = 0x42;

        rom[0x4020] = ADC_X_IND;
        rom[0x4021] = 0x20;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        cpu.rx = 0x04;

        for _ in 0..6 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }

    #[test]
    fn adc_indirect_y() {
        let mut rom = [NOP; u16::MAX as usize + 1];
        rom[0x0086] = 0x28;
        rom[0x0087] = 0x40;
        rom[0x4038] = 0x42;

        rom[0x4020] = ADC_IND_Y;
        rom[0x4021] = 0x86;

        rom[0xfffc] = 0x20;
        rom[0xfffd] = 0x40;

        let mut cpu = Mos6502::new(rom);
        cpu.ry = 0x10;

        for _ in 0..5 {
            cpu.cycle()
        }

        assert_eq!(cpu.ra, 0x42);
    }
}
