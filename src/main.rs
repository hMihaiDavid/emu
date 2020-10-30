mod vm;
mod vm_mem;

use std::path::Path;

use vm::Vm;
use vm_mem::VirtAddr;
use vm_mem::{Perm, PERM_WRITE, PERM_READ, PERM_EXEC, PERM_RAW};

pub fn main() {
    //println!("Hello, world!");
    /*let m = Vm::new(8);
    let data = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let mut buf: [u8; 2] = [0; 2];
    
    let mut mm = m.mem;
    mm.set_perms(VirtAddr(0), 8, Perm(PERM_WRITE | PERM_READ));
    mm.write(VirtAddr(0), &data[0..]).unwrap(); // Fill memory.
    mm.read(VirtAddr(3), &mut buf[..]).unwrap();
    mm.write(VirtAddr(0), &data[0..]).unwrap(); // Fill memory.
    mm.set_perms(VirtAddr(0), 8, Perm(PERM_EXEC));
    mm.read_exec(VirtAddr(3), &mut buf[..]).unwrap();

    println!("{:?}", buf);
    */

    /*
    let mut m = Vm::new(8*1024*1024);
    match m.map_elf(Path::new("../../foo")) {
        Err(m) => panic!("Cannot map ELF: {}", m),
        _ => () ,
    }
    let mut buf = [0u8; 0xde9];
    m.mem.read(VirtAddr(0x4926a4), &mut buf).unwrap();
    println!("{:#x?}", &buf[..]);
    */
    
    /*let mut m = Vm::new(8*1024*1024);
    match m.map_elf(Path::new("../../foo")) {
        Err(m) => panic!("Cannot map ELF: {}", m),
        _ => () ,
    }*/

    let mut m = Vm::new(8*1024*1024);
    //let load_info = 
    match m.map_elf(Path::new("../../foo")) {
        Err(m) => panic!("Cannot map ELF: {}", m),
        _ => { }
        //load_info => load_info,
    };

    m.load_symbols();

    //m.setup_abi_stack();
    //m.run_interpreted().unwrap();
    

    
 
    let mut buf = [0x41u8, 0x41, 0x41, 0x41];
    let mut m2 = m.fork();
    m2.mem.write_ignore_perms(VirtAddr(0x4005d0), &buf[..]); // overwrite first instruction.
    m2.reset(&m);
    //use vm_mem::PERM_RAW;
    //m2.mem.add_perms(VirtAddr(0), 100, Perm(PERM_READ | PERM_RAW));
   
    use crate::vm::GReg;
    let st = m2.mem.grow_stack(2*1024*1024).unwrap().0;
    m2.mem.add_perms(VirtAddr(st+(2*1024*1024)-256), 256, // libc does uninit read? 
                     Perm(PERM_RAW)).unwrap();
    
    //m2.set_gpr(GReg::Sp as usize, (m2.mem.mem.len()-1i28) as u32); 
    let mut p = m2.mem.mem.len()&0xffffffff0;
    
    p = p - 16;
    m2.mem.write(VirtAddr(p),
    b"\x69\x03\xcb\xf0\x00\x5e\xf8\x32\x31\x2b\xc5\xf0\x67\x5c\xa4\x4b"); 
    
    let rand16_addr = unsafe {
        core::slice::from_raw_parts(&(p as u32) as *const u32 as *const u8, 4) };

    p = p - 4;
    m2.mem.write(VirtAddr(p), b"foo\x00"); let arg0_addr = p;
    
    
    // auxv
    p = p - 8;
    m2.mem.write(VirtAddr(p), b"\x00\x00\x00\x00\x00\x00\x00\x00"); // auxv end
    
    /*p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x00\x10\x00\x00");
    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x06\x00\x00\x00"); // AT_PAGESZ*/
    
    /*p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x00\x00\x00\x00");
    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x03\x00\x00\x00"); // AT_PHDR

    // TODO: TIMER COUNT THING AND MAYBE EUID...

    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x20\x00\x00\x00");
    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x04\x00\x00\x00"); // AT_PHENT


    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x09\x00\x00\x00");
    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x05\x00\x00\x00"); // AT_PHNUM
    */
    /*p = p - 4;
    //m2.mem.write(VirtAddr(p), b"\xc0\xc0\xc0\xc0");
    m2.mem.write(VirtAddr(p), b"\x00\x00\x00\x00");
    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x0f\x00\x00\x00"); // AT_PLATFORM*/

    p = p - 4;  // AT_RANDOM is necessary or it triggers a nullptr deref in libc.
    m2.mem.write(VirtAddr(p), rand16_addr);
    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x19\x00\x00\x00"); // AT_RANDOM


    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x00\x00\x00\x00"); // null env

    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x00\x00\x00\x00"); // end argv pointers
    p = p - 4;
    let arg0 = b"\x0c\xff\x7f\x00";//       "0x7fff0c";
    m2.mem.write(VirtAddr(p), arg0); // arg0

    p = p - 4;
    m2.mem.write(VirtAddr(p), b"\x01\x00\x00\x00"); // argc = 1;

    m2.set_gpr(GReg::Sp as usize, p as u32);

    //let brk = m2.mem.brk(VirtAddr(0)).ok_or(()).unwrap();
    //m2.mem.brk(VirtAddr(brk+1024));
    
    m2.run_interpreted().unwrap();


}

