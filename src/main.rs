mod vm;
mod vm_mem;

use std::path::Path;

use vm::Vm;
use vm_mem::VirtAddr;
use vm_mem::{Perm, PERM_WRITE, PERM_READ, PERM_EXEC };

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
    match m.map_elf(Path::new("../../bar")) {
        Err(m) => panic!("Cannot map ELF: {}", m),
        _ => () ,
    }
    
    let mut buf = [0x41u8, 0x41, 0x41, 0x41];
    let mut m2 = m.fork();
    m2.mem.write_ignore_perms(VirtAddr(0x4005d0), &buf[..]); // overwrite first instruction.
    m2.reset(&m);
    //use vm_mem::PERM_RAW;
    //m2.mem.add_perms(VirtAddr(0), 100, Perm(PERM_READ | PERM_RAW));
   
    use crate::vm::GReg;
    let st = m2.mem.grow_stack(1024*1024).unwrap();

    m2.set_gpr(GReg::Sp as usize, (m2.mem.mem.len()-16) as u32); 
    

    //let brk = m2.mem.brk(VirtAddr(0)).ok_or(()).unwrap();
    //m2.mem.brk(VirtAddr(brk+1024));

    println!("top of stack right before run: {:#x}", m2.gpr(GReg::Sp as usize));
    m2.run_interpreted().unwrap();


}

