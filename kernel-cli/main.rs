#![allow(clippy::read_zero_byte_vec)]

fn main() -> process::ExitCode {
    env_logger::builder()
        .target(env_logger::Target::Stdout)
        .init();

    match try_main() {
        Ok(()) => process::ExitCode::SUCCESS,
        Err(e) => {
            println!("Error: {e}");
            process::ExitCode::FAILURE
        }
    }
}

fn try_main() -> io::Result<()> {
    let mut args = env::args_os().skip(1);
    let Some(program) = args.next() else {
        return Err(io::Error::other("missing arguments"));
    };
    let mut child = process::Command::new(program)
        .args(args)
        .stdout(process::Stdio::piped())
        .spawn()?;

    let mut kernel = kernel::Kernel::new();
    let mut pipe = child.stdout.take().unwrap();

    let mut message_len = [0_u8; 4];
    let mut message = Vec::new();
    loop {
        match pipe.read_exact(&mut message_len) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
            Err(e) => return Err(e),
        }
        let message_len = u32::from_le_bytes(message_len) as usize;
        message.resize(message_len, 0);
        pipe.read_exact(&mut message)?;
        let message = str::from_utf8(&message).map_err(io::Error::other)?;
        if let Err(e) = kernel.add(message) {
            println!("{e}");
        }
    }
    Ok(())
}

use std::env;
use std::io;
use std::io::Read as _;
use std::process;
use std::str;
