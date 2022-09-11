/*
 * Copyright (C) 2022 taylor.fish <contact@taylor.fish>
 *
 * This file is part of Base116.
 *
 * Base116 is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Base116 is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with Base116. If not, see <https://www.gnu.org/licenses/>.
 */

use std::env;
use std::io;
use std::iter::FromIterator;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn compile<P: AsRef<Path>>(path: P) -> io::Result<bool> {
    let mut out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    out.push("feature-test");
    Ok(Command::new(env::var_os("RUSTC").unwrap())
        .arg(path.as_ref())
        .arg("-o")
        .arg(out)
        .arg("--crate-type=lib")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()?
        .success())
}

fn main() -> io::Result<()> {
    env::set_current_dir(PathBuf::from_iter(["misc", "feature-test"]))?;
    if compile("unsafe_op_in_unsafe_fn.rs")? {
        println!("cargo:rustc-cfg=has_unsafe_op_in_unsafe_fn");
    }
    Ok(())
}
