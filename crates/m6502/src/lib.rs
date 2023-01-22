//! This crate contains constants relating to the
//! [M6502](https://en.wikipedia.org/wiki/MOS_Technology_6502).

/// Status register flag bitmasks.
#[allow(non_snake_case)]
pub mod SR {
    /// Negative
    pub const N: u8 = 0x80;
    /// Overflow
    pub const V: u8 = 0x40;
    /// Break
    pub const B: u8 = 0x10;
    /// Decimal
    pub const D: u8 = 0x08;
    /// Interrupt
    pub const I: u8 = 0x04;
    /// Zero
    pub const Z: u8 = 0x02;
    /// Carry
    pub const C: u8 = 0x01;
}

/// Reference: <https://www.masswerk.at/6502/6502_instruction_set.html>.
#[allow(non_snake_case)]
pub mod opcodes {
    pub const NOP: u8 = 0xea;
    // Stack
    pub const PHA: u8 = 0x48;
    pub const PLA: u8 = 0x68;
    /// Add Memory to Accumulator with Carry.
    ///
    /// A + M + C -> A, C
    pub mod ADC {
        pub const IMM: u8 = 0x69;
        pub const ZPG: u8 = 0x65;
        pub const ZPG_X: u8 = 0x75;
        pub const ABS: u8 = 0x6d;
        pub const ABS_X: u8 = 0x7d;
        pub const ABS_Y: u8 = 0x79;
        pub const X_IND: u8 = 0x61;
        pub const IND_Y: u8 = 0x71;
    }
    /// Shift Left One Bit (Memory or Accumulator)
    ///
    /// C <- \[76543210\] <- 0
    pub mod ASL {
        pub const ACC: u8 = 0x0a;
        pub const ZPG: u8 = 0x06;
        pub const ZPG_X: u8 = 0x16;
        pub const ABS: u8 = 0x0e;
        pub const ABS_X: u8 = 0x1e;
    }
    /// Branch on C = 0.
    pub const BCC: u8 = 0x90;
    /// Branch on C = 1.
    pub const BCS: u8 = 0xb0;
    /// Branch on Z = 1.
    pub const BEQ: u8 = 0xf0;
    /// Branch on N = 1.
    pub const BMI: u8 = 0x30;
    /// Branch on Z = 0.
    pub const BNE: u8 = 0xd0;
    /// Branch on N = 0.
    pub const BPL: u8 = 0x10;
    /// Branch on V = 0.
    pub const BVC: u8 = 0x50;
    /// Branch on V = 1.
    pub const BVS: u8 = 0x70;
    /// Force Break
    ///
    /// BRK initiates a software interrupt similar to a hardware
    /// interrupt (IRQ). The return address pushed to the stack is
    /// PC+2, providing an extra byte of spacing for a break mark
    /// (identifying a reason for the break.)
    /// The status register will be pushed to the stack with the break
    /// flag set to 1. However, when retrieved during RTI or by a PLP
    /// instruction, the break flag will be ignored.
    /// The interrupt disable flag is not set automatically.
    pub const BRK: u8 = 0x00;
    /// Test Bits in Memory with Accumulator.
    ///
    /// Bits 7 and 6 of operand are transfered to bit 7 and 6 of SR (N,V);
    /// the zero-flag is set to the result of operand AND accumulator.
    pub mod BIT {
        pub const ZPG: u8 = 0x24;
        pub const ABS: u8 = 0x2c;
    }
    // SBC
    pub const SBC_IMM: u8 = 0xe9;
    pub const SBC_ZPG: u8 = 0xe5;
    /// AND Memory with Accumulator.
    pub mod AND {
        pub const IMM: u8 = 0x29;
        pub const ZPG: u8 = 0x25;
        pub const ZPG_X: u8 = 0x35;
        pub const ABS: u8 = 0x2d;
        pub const ABS_X: u8 = 0x3d;
        pub const ABS_Y: u8 = 0x39;
        pub const X_IND: u8 = 0x21;
        pub const IND_Y: u8 = 0x31;
    }
    /// Compare Memory with Accumulator.
    pub mod CMP {
        pub const IMM: u8 = 0xc9;
        pub const ZPG: u8 = 0xc5;
        pub const ZPG_X: u8 = 0xd5;
        pub const ABS: u8 = 0xcd;
        pub const ABS_X: u8 = 0xdd;
        pub const ABS_Y: u8 = 0xd9;
        pub const X_IND: u8 = 0xc1;
        pub const IND_Y: u8 = 0xd1;
    }
    /// Decrement Memory by One.
    ///
    /// M - 1 -> M
    pub mod DEC {
        pub const ZPG: u8 = 0xc6;
        pub const ZPG_X: u8 = 0xd6;
        pub const ABS: u8 = 0xce;
        pub const ABS_X: u8 = 0xde;
    }
    /// Decrement Index X by One
    ///
    /// X - 1 -> X
    pub const DEX: u8 = 0xca;
    /// Load Accumulator with Memory
    ///
    ///M -> A
    pub mod LDA {
        pub const IMM: u8 = 0xa9;
        pub const ZPG: u8 = 0xa5;
    }
    /// Store Accumulator in Memory
    pub mod STA {
        pub const ZPG: u8 = 0x85;
    }

    /// Clear carry flag.
    pub const CLC: u8 = 0x18;
    /// Clear decimal mode.
    pub const CLD: u8 = 0xd8;
    /// Clear interrupt disable bit.
    pub const CLI: u8 = 0x58;
    /// Clear overflow flag.
    pub const CLV: u8 = 0xb8;
    pub const SEC: u8 = 0x38;
}
