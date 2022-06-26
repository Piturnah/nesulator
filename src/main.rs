// References: https://www.masswerk.at/6502/6502_instruction_set.html

use std::{fmt, ops::Shl};

// Opcodes
const ADC_IMM: u8 = 0x69;
const ADC_ZPG: u8 = 0x65;
const ADC_ZPG_X: u8 = 0x75;
const ADC_ABS: u8 = 0x6d;
const ADC_ABS_X: u8 = 0x7d;
const ADC_ABS_Y: u8 = 0x79;
const NOP: u8 = 0xea;

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
    fn fetch(&mut self) -> u8 {
        // lobyte
        let mut fetch_addr: usize = self.mem[self.pc as usize] as usize;
        // hibyte
        fetch_addr += (self.mem[self.pc as usize + 1] as usize).shl(8);

        self.mem[fetch_addr]
    }

    // Add lhs and rhs, enable SR carry bit if there is carry
    fn add_with_carry(&mut self, lhs: u8, rhs: u8) -> u8 {
        match lhs.checked_add(rhs) {
            Some(val) => val,
            None => {
                self.sr |= SR_C;
                lhs.wrapping_add(rhs)
            }
        }
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
                        // Clear carry flag
                        self.sr &= !SR_C;

                        // Cache signs
                        let ra_sign = self.ra & SIGN;
                        let operand_sign = self.mem[self.pc as usize] & SIGN;

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
                            addr_mode => todo!("Handling of ADC for {:?}", addr_mode),
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
                    op => todo!("Implement handling for {op:?}"),
                }
            }

            (op, cycles) => self.current_instruction = Some((*op, cycles - 1)),
        }
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

#[cfg(test)]
mod test {
    use crate::*;

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
}
