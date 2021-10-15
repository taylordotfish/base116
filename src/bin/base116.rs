/*
 * Copyright (C) 2021 taylor.fish <contact@taylor.fish>
 *
 * This file is part of base116.
 *
 * base116 is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * base116 is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with base116. If not, see <https://www.gnu.org/licenses/>.
 */

use std::ffi::OsStr;
use std::fmt::{Debug, Display};
use std::fs::File;
use std::io::{stdin, stdout, BufReader, BufWriter, Read, Stdout, Write};
use std::path::Path;
use std::process::exit;

use base116::decode::{decode_bytes_with, DecodeConfig};
use base116::encode::{encode_to_bytes_with, EncodeConfig};

const USAGE: &str = "\
Usage: base116 [options] [file]

Encodes or decodes base-116 data from [file] and writes the result to standard
output. If [file] is missing or -, the data is read from standard input.

Options:
  -d --decode   Decode data instead of encoding

  --no-wrapper  When decoding, don't require wrapping 'Ǳ' and 'ǲ' characters.
                When encoding, don't output wrapper characters.

  --relaxed     When decoding, ignore trailing data after ending 'ǲ'
                character. Also ignore data before starting 'Ǳ' character,
                unless --no-wrapper is set.

  -h --help     Show this help message
  -v --version  Show program version
";

#[macro_use]
mod error_exit {
    use super::{exit, Display};

    macro_rules! error_exit {
        ($($args:tt)*) => {
            crate::error_exit::__run(format_args!($($args)*));
        };
    }

    #[doc(hidden)]
    pub fn __run(args: impl Display) -> ! {
        eprintln!("error: {}", args);
        if cfg!(feature = "cli-panic") {
            panic!("error: {}", args);
        } else {
            exit(1);
        }
    }
}

fn expect<T, E: Debug>(result: Result<T, E>, msg: impl Display) -> T {
    result.unwrap_or_else(|e| {
        eprintln!("error: {}", msg);
        if cfg!(feature = "cli-panic") {
            panic!("error: {}: {:?}", msg, e);
        } else {
            exit(1);
        }
    })
}

struct ParsedArgs<'a> {
    pub decode: bool,
    pub wrap: bool,
    pub relaxed: bool,
    pub path: Option<&'a Path>,
}

fn show_usage() -> ! {
    print!("{}", USAGE);
    exit(0);
}

fn show_version() -> ! {
    println!("{}", env!("CARGO_PKG_VERSION"));
    exit(0);
}

macro_rules! args_error {
    ($($args:tt)*) => {
        error_exit!(
            "{}\n{}",
            format_args!($($args)*),
            "See `base116 --help` for usage information.",
        );
    };
}

fn parse_args<'a, Args>(args: Args) -> ParsedArgs<'a>
where
    Args: IntoIterator<Item = &'a OsStr>,
{
    let mut decode = false;
    let mut wrap = true;
    let mut relaxed = false;
    let mut file: Option<&'a OsStr> = None;
    let mut options_done = false;

    let mut process_arg = |arg: &'a OsStr, astr: &str| {
        match astr {
            _ if options_done => {}
            "-" => {}
            "--" => {
                options_done = true;
                return;
            }
            "--help" => show_usage(),
            "--version" => show_version(),
            "--decode" => {
                decode = true;
                return;
            }
            "--no-wrapper" => {
                wrap = false;
                return;
            }
            "--relaxed" => {
                relaxed = true;
                return;
            }
            s if s.starts_with("--") => {
                args_error!("unrecognized option: {}", s);
            }
            s if s.starts_with('-') => {
                s.chars().skip(1).for_each(|c| match c {
                    'h' => show_usage(),
                    'v' => show_version(),
                    'd' => {
                        decode = true;
                    }
                    c => {
                        args_error!("unrecognized option: -{}", c);
                    }
                });
                return;
            }
            _ => {}
        }
        if file.replace(arg).is_some() {
            args_error!("unexpected argument: {}", astr);
        }
    };

    args.into_iter()
        .map(|a| (a, a.to_string_lossy()))
        .for_each(|(arg, astr)| process_arg(arg, &*astr));

    if relaxed && !decode {
        args_error!("--relaxed is allowed only when decoding");
    }

    ParsedArgs {
        decode,
        wrap,
        relaxed,
        path: file.map(Path::new),
    }
}

fn flush_stdout(writer: &mut BufWriter<Stdout>) {
    expect(writer.flush(), "could not write to standard output");
}

fn encode(stream: &mut impl Read, config: EncodeConfig) {
    let reader = BufReader::new(stream);
    let mut writer = BufWriter::new(stdout());
    encode_to_bytes_with(
        reader.bytes().map(|b| expect(b, "could not read input")),
        config,
    )
    .for_each(|b| {
        expect(writer.write_all(&[b]), "could not write to standard output");
    });
    flush_stdout(&mut writer);
}

fn decode(stream: &mut impl Read, config: DecodeConfig) {
    let reader = BufReader::new(stream);
    let mut writer = BufWriter::new(stdout());
    decode_bytes_with(
        reader.bytes().map(|b| expect(b, "could not read input")),
        config,
    )
    .for_each(|b| match b {
        Ok(b) => {
            expect(
                writer.write_all(&[b]),
                "could not write to standard output",
            );
        }
        Err(e) => {
            flush_stdout(&mut writer);
            error_exit!("input is not valid base-116 data: {}", e);
        }
    });
    flush_stdout(&mut writer);
}

fn main() {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let ParsedArgs {
        decode: should_decode,
        wrap,
        relaxed,
        path,
    } = parse_args(args.iter().map(|s| s.as_os_str()));

    let mut encode_config = EncodeConfig::new();
    encode_config.add_wrapper = wrap;

    let mut decode_config = DecodeConfig::new();
    decode_config.require_wrapper = wrap;
    decode_config.relaxed = relaxed;

    path.map(|path| {
        File::open(path).unwrap_or_else(|e| {
            error_exit!("could not open file '{}': {}", path.display(), e);
        })
    })
    .map_or_else(
        || {
            if should_decode {
                decode(&mut stdin(), decode_config);
            } else {
                encode(&mut stdin(), encode_config);
            }
        },
        |mut file| {
            if should_decode {
                decode(&mut file, decode_config);
            } else {
                encode(&mut file, encode_config);
            }
        },
    );
}
