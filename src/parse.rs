use nom::{
    bytes::complete::{tag, take},
    error::Error,
    IResult,
};
use std::{fmt, process};

pub struct ROM<'a> {
    prg: &'a [u8],
}

impl<'a> fmt::Debug for ROM<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        const WIDTH: usize = 16;
        let lines: Vec<_> = self.prg.chunks(WIDTH).enumerate().collect();
        for (i, line) in &lines {
            write!(f, "{i:04x}: ")?;
            for byte in line.iter() {
                write!(f, "{byte:02x} ")?;
            }
            if *i != lines.len() {
                writeln!(f, "")?;
            }
        }
        Ok(())
    }
}

fn parse_magic<'a>(input: &'a [u8]) -> IResult<&'a [u8], &[u8]> {
    tag(b"NES\x1a")(input)
}

pub fn parse_rom<'a>(input: &'a [u8]) -> IResult<&'a [u8], ROM> {
    let (input, _) = parse_magic(input).unwrap_or_else(|_| {
        eprintln!("Not a valid `.nes` file!");
        process::exit(1);
    });

    let take_bytes =
        |num: usize, input| take::<_, _, Error<_>>(num)(input).expect("unexpected EOF");

    let (input, prg_length) = take_bytes(1, input);

    let (input, _chr_length) = take_bytes(1, input);

    let (input, flags_6) = take_bytes(1, input);
    let (input, _flags_7) = take_bytes(1, input);
    let (input, _flags_8) = take_bytes(1, input);
    let (input, _flags_9) = take_bytes(1, input);
    let (input, _flags_10) = take_bytes(1, input);

    let (input, _padding) = take_bytes(4, input);

    // Check for 512-byte trainer before PRG
    let (input, _trainer) = take_bytes(
        match flags_6[0] & 0x8u8 > 0 {
            true => 512,
            false => 0,
        },
        input,
    );

    let (input, prg) = take_bytes(prg_length[0] as usize * 16_000, input);

    Ok((input, ROM { prg }))
}

#[cfg(test)]
mod test {
    use super::*;
    use std::fs;

    #[test]
    fn parse_magic_test() {
        let bytes = [
            0x4e, 0x45, 0x53, 0x1a, 0x02, 0x02, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00,
        ];

        let (_, magic) = parse_magic(&bytes).unwrap();
        assert_eq!(magic, b"NES\x1a");
    }

    #[test]
    fn dont_parse_magic() {
        let bytes = fs::read("./src/parse.rs").unwrap();
        assert!(parse_magic(&bytes).is_err());
    }

    #[test]
    #[ignore]
    fn parse_tetris() {
        let tetris = fs::read("/home/pit/Downloads/tetris.nes").unwrap();
        parse_rom(&tetris).unwrap();
    }
}
