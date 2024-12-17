use std::process::Command;
use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt;

extern crate cc;

fn main() {
    let mut cc = cc::Build::new();
    cc.file("../../C/rev_ffi.c");
    let bytes = Command::new("leanc").args(["--print-cflags"]).output().unwrap().stdout;
    let s = OsStr::from_bytes(&bytes).to_str().unwrap();
    for flag in s.split(" ") {
        let flag = flag.trim();
        cc.flag(flag);
    }
    cc.compile("rev_ffi");
}
