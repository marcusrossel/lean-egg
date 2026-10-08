use std::process::Command;

extern crate cc;

fn main() {
    let mut cc = cc::Build::new();
    cc.file("../../C/rev_ffi.c");
    let bytes = Command::new("leanc").args(["--print-cflags"]).output().unwrap().stdout;
    let s = String::from_utf8(bytes).unwrap();
    for flag in s.split(" ") {
        let flag = flag.trim();
        cc.flag(flag);
    }
    cc.compile("rev_ffi");
}
