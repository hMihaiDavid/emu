use std::path::Path;
use std::collections::BTreeMap;
use std::process::Command;

use crate::vm_mem::{Mem, VirtAddr, Perm, PERM_READ, PERM_WRITE, PERM_EXEC,
                    PERM_RAW};

//// General purpose register indeces used to index `Vm::gprs`.
#[repr(usize)]
//#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GReg {
    Zero  = 0,
    At, // 1
    V0, // 2
    V1, // 3
    A0, // 4
    A1, // 5
    A2, // 6
    A3, // 7
    T0, // 8
    T1, // 9 
    T2, // 10
    T3, // 11
    T4, // 12
    T5, // 13
    T6, // 14
    T7, // 15
    S0, // 16
    S1, // 17
    S2, // 18
    S3, // 19
    S4, // 20
    S5, // 21
    S6, // 22
    S7, // 23
    T8, // 24
    T9, // 25
    K0, // 26
    K1, // 27
    Gp, // 28
    Sp, // 29
    S8, // aka fp, stack frame pointer or subroutine variable.
    Ra, // 31
}

/*//// Special purpose register indeces used to index `Vm::sprs`.
#[repr(usize)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SReg {
    HI = 0,
    LO,
    Pc,
}*/

#[derive(Debug)]
struct RFormat {
    funct: u8,
    shamt: u8,
    rd:    usize,
    rt:    usize,
    rs:    usize,
}

impl From<u32> for RFormat {
    fn from(inst: u32) -> Self {
        RFormat {
            funct: (inst & 0x3f ) as u8,             // lower 6 bits
            shamt: ( (inst >> 6) & 0x1f) as u8,      // next  5 bits
            rd   : ( (inst >> 11) & 0x1f) as usize,  // next  5 bits 
            rt   : ( (inst >> 16) & 0x1f) as usize,  // next  5 bits 
            rs   : ( (inst >> 21) & 0x1f) as usize,  // next  5 bits 
        }
    }
}

#[derive(Debug)]
struct IFormat {
    offset: u16, // remember to do as i16 as whatever to sign extend.
    rt: usize,
    rs: usize,
}

impl From<u32> for IFormat {
    fn from(inst: u32) -> Self {
        IFormat {
            offset: (  inst & 0xffff) as u16,
            rt:     ( (inst >> 16) & 0x1f) as usize,
            rs:     ( (inst >> 21) & 0x1f) as usize,
        }
    }
}

#[derive(Debug)]
struct JFormat {
    // TODO
}


/// Reasons for VM exit.
//#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum VmExit {
    /// Attempted to read non-readable memory at `VirtAddr`.
    ReadFault(VirtAddr),
    /// Attempted to write non-writable memory at `VirtAddr`.
    WriteFault(VirtAddr),
    /// Attempted to execute non-executable memory at `VirtAddr`.
    /// This has priority over `ReadUninit`.
    ExecFault(VirtAddr),
    /// Attempted to read uninitialized memory at `VirtAddr`.
    /// This has priority over `ReadFault`.
    ReadUninit(VirtAddr),
    
    /// An address calculation using `VirtAddr` overflowed.
    AddrOverflow(VirtAddr), 
    /// Instruction at pc `VirtAddr` raised an Integer Overflow.
    IntegerOverflow(VirtAddr),
    /// An invalid instruction at `VirtAddr` attempted execution. 
    IllegalInstruction(VirtAddr),
    /// Instruction at address `VirtAddr` signaled a trap with code `u32`.
    /// Example: TEQ with code 7 is a division by zero in linux abi I think (?)
    TrapException(VirtAddr, u32),
    
    /// Normal exit with status code `i32`
    Finish(i32),

    /// Collision between data segment and stack segment. This happens
    /// because of brk() or when growing stack.
    SegmentOverflow,
}

#[repr(C)]
#[derive(Default, Debug)]
/// https://elixir.bootlin.com/linux/latest/source/arch/mips/include/uapi/asm/stat.h#L52
struct Stat64 {
   st_dev:   u32,
   st_pad0:  [u32; 3],
   st_ino:   u64,
   st_mode:  u32,
   st_nlink: u32,
   st_uid:   u32,
   st_gid:   u32,
   st_rdev:  u32,
   st_pad1:  [u32; 3],
   st_size:  u64,
   st_atime: u32,
   st_atime_nsec: u32,
   st_mtime: u32,
   st_mtime_nsec: u32,
   st_ctime: u32,
   st_ctime_nsec: u32,
   st_blksize:    u32,
   st_pad2:  u32,
   st_blocks: u64,
}

// A linux SysV abi MIPS II LE emulated guest.
pub struct Vm {
    pub GPR:  [u32; 32],
    pub FPR:  [u32; 32],
    pub HI:   u32,
    pub LO:   u32,
    pub Pc:   u32,
    pub CP0_UserLocal: u32,
    pub mem:  Mem,

    // These are text symbols (T and t) from the binary parsed with
    // GNU nm.
    pub sym_to_va: BTreeMap<String, VirtAddr>,
    pub va_to_sym: BTreeMap<VirtAddr, String>,
}

impl Vm {
    pub fn new(mem_size: usize) -> Self {
        assert!(mem_size != 0);
        Vm { // TODO implement trait Default
            GPR:  [0; 32],
            FPR:  [0; 32],
            HI:   0u32,
            LO:   0u32,
            Pc:   0u32, // TODO CHECK proper initial state.
            CP0_UserLocal: 0,
            mem:   Mem::new(mem_size),

            sym_to_va: BTreeMap::new(),
            va_to_sym: BTreeMap::new(),
        }
    }
    
    /// Returns a new `Vm` wihch has a shallow copy of `self`'s state but
    /// with the memory marked as non-dirty. You can call `reset()` on the
    /// returned `Vm` and it will be differentially restored to the state
    /// when the fork happened.
    pub fn fork(&self) -> Vm {
        Vm {
            GPR: self.GPR.clone(),
            FPR: self.FPR.clone(),
            HI:  self.HI.clone(),
            LO:  self.LO.clone(),
            Pc:  self.Pc.clone(),
            CP0_UserLocal: self.CP0_UserLocal.clone(),

            mem: self.mem.fork(),

            sym_to_va: self.sym_to_va.clone(),
            va_to_sym: self.va_to_sym.clone(),
        }
    }
    
    pub fn reset(&mut self, prev: &Vm) -> () {
        self.GPR = prev.GPR;
        self.FPR = prev.FPR;
        self.HI  = prev.HI;
        self.LO  = prev.LO;
        self.Pc  = prev.Pc;
        self.CP0_UserLocal = prev.CP0_UserLocal;

        self.mem.reset(&prev.mem);
        
        // Symbols remain the same, once parsed they never change.
    }

    #[inline]
    pub fn gpr(&self, reg: usize) -> u32 {
        if reg == 0 {
            0
        } else {
            self.GPR[reg as usize]
        }
    }

    #[inline]
    pub fn set_gpr(&mut self, reg: usize, val: u32) -> () {
        if reg == 0 {
            return;
        }
        self.GPR[reg as usize] = val;
    }
    
    #[inline]
    pub fn pc(&self) -> u32 {       
        self.Pc
    }
    
    #[inline]
    pub fn set_pc(&mut self, val: u32) -> () {
        self.Pc = val;
    }

    pub fn load_symbols(&mut self) -> Result<(), u32> {  
        //unimplemented!();

        let out = Command::new("nm")
            .arg("-S") // displat size of symbols.
            //.arg("-a") // include debugging symbols.
            .arg("../../foo")
            .output()
            .expect("failed to execute nm");
        
        assert!(out.status.success(), "nm returned error");
        let stdout = core::str::from_utf8(&out.stdout)
            .expect("Failed to get nm output as String");

        // Parse nm output to gather text (T and t) symbols.
        for line in stdout.lines() {
            let mut v = line.split_whitespace();
            if v.clone().count() != 4 { continue; }
            
            let addr = usize::from_str_radix(v.next().unwrap(), 16).unwrap();
            let _size = usize::from_str_radix(v.next().unwrap(), 16).unwrap();
            let flag = v.next().unwrap();
            if flag != "T" && flag != "t" { continue; }
            let name = String::from(v.next().unwrap());
            let name_cpy = name.clone();
            let _end = addr.checked_add(_size).unwrap();
            
            self.sym_to_va.insert(name, VirtAddr(addr));
            self.va_to_sym.insert(VirtAddr(addr), name_cpy);
        }

        println!("{:?}", self.va_to_sym.range(..=va).next_back()
                 .get_key_value(VirtAddr(0x42014c)));
        panic!();
    
        Ok(()) 
    }

    pub fn get_sym_off(&self, va: VirtAddr) -> Option<(&str, usize)> {
        unimplemented!();  
        
    }

    /// Enter into the guest VM and continue running until next exit.
    /// The `VmExit` reason is returned.
    /// This function emulates the guest in a slow fetch-decode-execute
    /// loop instruction by instruction, it doesn't use a JIT.
    pub fn run_interpreted(&mut self) -> Result<(), VmExit> {
        let mut jmp_target: Option<u32> = None;

        'next_instr: loop {
            let pc: u32    = self.pc();

            let instr: u32 = self.mem.read_u32_le_exec(
                                        VirtAddr(pc as usize))?; 
            let mut atomic_update = false;
            let instr_val = instr;
            
            //println!("Executing instruction {:x} @ pc {:#x}", instr_val, pc);

            // the following commented block proves that the _setjmp
            // in libc_start_main does not return properly, it jumps randomly.
            /*if pc == 0x00406740 { // _setjmp()
                println!("MEMES");
            } else if pc == 0x400a00 {
                // after call to _setjmp() in __libc_start_main()
                panic!("REACHED AFTER _setjmp()");
            }*/

            /*if pc == 0x4005e8 {
                panic!("GP: {:#x}", self.gpr(GReg::Gp as usize));
            }*/

            //if pc == 0x4363b0 {panic!();}

            match (instr >> 26) as u8 { // higher 6 bits or op.
                0b00_110011 => {
                    // PREF
                    // Do nothing.
                    //panic!("pref @ pc {:#x}", pc);
                },

                0b00_111101 => {
                    // SDC1 (fp) used by _setjmp to store fp into env
                    //panic!();
                    let instr = IFormat::from(instr);
                    let effaddr = (instr.offset as i16 as i32 as u32)
                                  .wrapping_add(self.gpr(instr.rs) as u32)
                        as usize;
                    let lo = self.FPR[instr.rt];
                    let hi = self.FPR[instr.rt+1]; // XXX: this can panic.
                    self.mem.write_u32_le(VirtAddr(effaddr),   lo);
                    self.mem.write_u32_le(VirtAddr(effaddr+4), hi);

                },
                0b00_110101 => {
                    // LDC1
                    unimplemented!("LDC1");
                },

                0b00_011100 => { // SPECIAL2
                    let instr = RFormat::from(instr);
                    match instr.funct {
                        0b00_000010 => {
                            // MUL
                            if instr.shamt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                           VirtAddr(pc as usize)));
                            }
                            /*let mut hi: u32;
                            let lo = core::arch::x86_64::_mulx_u32(
                               self.gpr(instr.rs), self.gpr(instr.rt), &mut hi);
                            
                            self.set_gpr(instr.rd) = lo;*/
                            self.set_gpr(instr.rd,
                            ( (self.gpr(instr.rs)as i32) * 
                              (self.gpr(instr.rt)as i32) ) as u32
                            ); // TODO: Check if this is correct.
                        }

                        _ => {
                                unimplemented!("R SPECIAL2 {:#x} @ pc {:#x}",
                                                instr_val, pc);
                        },
                    }; // end match SPECIAL2
                
                },
                0b00_011111 => { // SPECIAL3
                    let instr = RFormat::from(instr);
                    match instr.funct {
                        0b00_100000 => {
                            // BSHFL
                            match instr.shamt {
                                0b000_11000 => {
                                    // SEH
                                    let v = self.gpr(instr.rt)
                                        as u16 as i16 as i32 as u32;
                                    self.set_gpr(instr.rd, v);
                                },
                                0b000_10000 => {
                                    // SEB
                                    let v = self.gpr(instr.rt)
                                        as u8 as i8 as i32 as u32;
                                    self.set_gpr(instr.rd, v);
                                },
                                _ => {
                                    unimplemented!("BSHFL @ pc {:#x}", pc);
                                }
                            }

                        },

                        0b00_111011 => {
                            // RDHWR
                            if instr.shamt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                           VirtAddr(pc as usize)));
                            }
                            //unimplemented!("RDHWR rd: {:?}", instr.rd);
                            if instr.rd == 29 {
                                self.set_gpr(instr.rt, self.CP0_UserLocal);
                                //println!("RDHWR cp0ul: {:#x}, rt: {:#x}",
                                //         self.CP0_UserLocal, self.gpr(instr.rt));
                            } else {
                                unimplemented!("RDHWR rd: {:?}", instr.rd);
                            }
                        },
                        0b00_000000 => {
                            // EXT
                            let lsb  = instr.shamt as u32;
                            let size = (instr.rd as u32)+1;
                            let rs   = self.gpr(instr.rs) as u32;
                            
                            let mask = (1 << size)-1;
                            let mut v = (rs >> lsb) & mask;
                            self.set_gpr(instr.rt, v);
                        },

                      _ => unimplemented!("SPECIAL3")
                    }
                },

                0b00_000010 => {
                    // J
                    let ta: u32 = (instr & 0x03ffffff) << 2;
                    jmp_target = Some(ta);
                    self.set_pc(pc.wrapping_add(4));
                    continue 'next_instr;

                },
                0b00_000011 => {
                    // JAL
                    // IMPORTANT:
                    // The upper four bits of target address are the corresponding
                    // bits of the address of the next instruction to this one (the slot).
                    // This is not relevant for userspace but take it into account since
                    // this emulator is not technically per spec. Life is tough.
                    // See page 195 of MD00086-2B-MIPS32BIS-AFP-6.06.pdf

                    self.set_gpr(31, pc.wrapping_add(8));
                    let ta: u32 = (instr & 0x03ffffff) << 2;
                    jmp_target = Some(ta);
                    //println!("DEBUG link to pc {:#x}", ta);
                    self.set_pc(pc.wrapping_add(4));
                    continue 'next_instr;
                },
                0b00_000100 => {
                    // BEQ
                    let instr = IFormat::from(instr);
                    
                    if self.gpr(instr.rs) == self.gpr(instr.rt) {
                        let of = (instr.offset as i16 as i32 as u32) << 2;
                        let ta = of.wrapping_add(pc.wrapping_add(4));
                        jmp_target = Some(ta);
                        /*if pc == 0x436404 {
                            panic!("AAAAAAA jmp_target: {:#x} next_pc: {:#x}", jmp_target.unwrap(),
                            pc.wrapping_add(4)
                            );
                        }*/
                        self.set_pc(pc.wrapping_add(4));
                        continue 'next_instr;
                    }
                    
                },
                0b00_000101 => {
                    // BNEQ
                    let instr = IFormat::from(instr);
                    
                    if self.gpr(instr.rs) != self.gpr(instr.rt) {
                        let of = (instr.offset as i16 as i32 as u32) << 2;
                        let ta = of.wrapping_add(pc.wrapping_add(4));
                        jmp_target = Some(ta);
                        // ME CAGO EN LA PUTA EL BUG ESTABA AQUÍ!!!!!!1
                        // JODERRRRRRRRRRRRRRRR!!!!
                        /*if pc == 0x436404 {
                            panic!("AAAAAAA jmp_target: {:#x} next_pc: {:#x}", jmp_target.unwrap(),
                            pc.wrapping_add(4)
                            );
                        }*/
                        self.set_pc(pc.wrapping_add(4));
                        continue 'next_instr;
                    }
                },

                0b00_000000 => { // SPECIAL
                    let instr = RFormat::from(instr);

                    match (instr.funct) as u8 {
                        0b00_001111 => {
                            // SYNC do nothing.
                            if ((instr_val >> 11) & 0x7fff) != 0 { 
                                return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }
                        },
                        0b00_000000 => {
                            // SLL
                            //panic!("la vie en rose");
                            if instr.rs != 0 {
                                return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }
                            // TODO: check shamt. rust panics when overflow
                            self.set_gpr(instr.rd,
                                         self.gpr(instr.rt) << instr.shamt);
                        },
                        0b00_000010 => {
                            // SRL
                            if instr.rs != 0 {
                                return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }

                            self.set_gpr(instr.rd,
                                         (self.gpr(instr.rt) as u32) 
                                         >> (instr.shamt) as u32);
                        },
                        0b00_000011 => {
                            // SRA
                            self.set_gpr(instr.rd,
                                ( (self.gpr(instr.rt) as i32) >>
                                  (instr.shamt as u32 as i32)
                                ) as u32
                            );
                        },

                        0b00_000100 => {
                            // SLLV
                            if instr.shamt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }
        // https://users.rust-lang.org/t/intentionally-overflow-on-shift/11859/5
        // https://bugs.chromium.org/p/nativeclient/issues/detail?id=245
                            // rust panics if you shift more than the
                            // number of bits in the integer you're shifting.
                            let rs = self.gpr(instr.rs) as u32;
                            if rs >= 32 {
                                self.set_gpr(instr.rd, 0);
                            } else {
                                self.set_gpr(instr.rd,
                                     (self.gpr(instr.rt) as u32)  << rs );
                            }
                        },
                        0b00_100101 => {
                            // OR
                            let res = self.gpr(instr.rs) | self.gpr(instr.rt);
                            self.set_gpr(instr.rd, res);
                            //println!("OR res = {:#x}", res);
                            //println!("rs: {:#x}, rt: {:#x}, rd:{:#x} instr.rs:{:#x}, instr.rt:{:#x}, instr.rd: {:#x}", self.gpr(instr.rs), self.gpr(instr.rt), self.gpr(instr.rd), instr.rs, instr.rt, instr.rd);
                            //println!("!! S8 = {:#x}", self.gpr(GReg::S8 as usize));
                        },
                        0b00_100110 => {
                            // XOR
                            let res = self.gpr(instr.rs) ^ self.gpr(instr.rt);
                            self.set_gpr(instr.rd, res);    
                        },
                        0b00_100100 => {
                            // AND
                            let res = self.gpr(instr.rs) & self.gpr(instr.rt);
                            self.set_gpr(instr.rd, res);    
                        },
                        0b00_100111 => {
                            // NOR
                            let res = self.gpr(instr.rs) | self.gpr(instr.rt);
                            self.set_gpr(instr.rd, !res); 
                        },
                        
                        0b00_100000 => {
                            // ADD
                            let res = self.gpr(instr.rs)
                                      .checked_add(self.gpr(instr.rt))
                            .ok_or(VmExit::IntegerOverflow(
                                           VirtAddr(pc as usize)))?;
                            
                            self.set_gpr(instr.rd, res);
                        },
                        0b00_100001 => {
                            // ADDU
                            let res = self.gpr(instr.rs)
                                      .wrapping_add(self.gpr(instr.rt));
                            self.set_gpr(instr.rd, res); 
                        },
                        0b00_100010 => {
                            // SUB
                            let res = self.gpr(instr.rs)
                                      .checked_sub(self.gpr(instr.rt))
                            .ok_or(VmExit::IntegerOverflow(
                                           VirtAddr(pc as usize)))?;
                            
                            self.set_gpr(instr.rd, res);
                        
                        },
                        0b00_100011 => {
                            // SUBU
                            let res = self.gpr(instr.rs)
                                      .wrapping_sub(self.gpr(instr.rt));
                            self.set_gpr(instr.rd, res); 
                        },
                        0b00_011011 => {
                            // DIVU
                            if instr.shamt != 0 || instr.rd != 0 {
                                return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize)));
                            }

                            let dividend: u32  = self.gpr(instr.rs);
                            let divisor:  u32  = self.gpr(instr.rt);
                            if divisor != 0 {
                                self.LO = dividend / divisor; // quotient
                                self.HI = dividend % divisor; // remainder
                            } // TODO: Check if this is correct.
                        },
                        0b00_011001 => {
                            // MULTU
                            if instr.shamt != 0 || instr.rd != 0 {
                                return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize)));
                            }
                            let rs = self.gpr(instr.rs);
                            let rt = self.gpr(instr.rt);
                            let mut hi: u32 = 0;
                            let lo = unsafe {
                                core::arch::x86_64::_mulx_u32(rs, rt, &mut hi)
                            };
                            self.HI = hi; self.LO = lo;
                        },
                        0b00_010010 => {
                            // MFLO
                            if instr.shamt != 0 || instr.rs != 0
                                || instr.rt != 0 {
                                    return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }
                            self.set_gpr(instr.rd, self.LO);


                        }, 
                        0b00_010000 => {
                            // MFHI
                            if instr.shamt != 0 || instr.rs != 0
                                || instr.rt != 0 {
                                    return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }
                            self.set_gpr(instr.rd, self.HI);
                        },

                        0b00_101011 => {
                            // SLTU
                            if instr.shamt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize)));
                            }

                            if (self.gpr(instr.rs) as i32)
                             < (self.gpr(instr.rt) as i32) {
                                self.set_gpr(instr.rd, 1);
                            } else {
                                self.set_gpr(instr.rd, 0);
                            }

                        },
                        0b00_101010 => {
                            // SLT
                            if instr.shamt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize)));
                            }

                            if (self.gpr(instr.rs) as u32)
                             < (self.gpr(instr.rt) as u32){
                                self.set_gpr(instr.rd, 1);
                            } else {
                                self.set_gpr(instr.rd, 0);
                            }

                        },

                        0b00_001011 => {
                            // MOVN
                            if instr.shamt != 0 {
                                 return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize))); 
                            }
                            if self.gpr(instr.rt) != 0 {
                                self.set_gpr(instr.rd, instr.rs as u32);
                            }
                        },
                        0b00_001010 => {
                            // MOVZ
                            if instr.shamt != 0 {
                                 return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize))); 
                            }
                            if self.gpr(instr.rt) == 0 {
                                self.set_gpr(instr.rd, instr.rs as u32);
                            }
                        },


                        0b00_001000 => {
                            // JR
                            if instr.rd != 0 || instr.rt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize)));
                            }

                            let target_pc = self.gpr(instr.rs);
                            jmp_target = Some(target_pc);
                            self.set_pc(pc.wrapping_add(4));
                            continue 'next_instr;
                        },
                        0b00_001001 => {
                            // JALR
                            if instr.rt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize)));
                            }
                            
                            self.set_gpr(instr.rd, pc.wrapping_add(8));
                            let target_pc = self.gpr(instr.rs);
                            jmp_target = Some(target_pc);
                            self.set_pc(pc.wrapping_add(4));
                            continue 'next_instr;

                        },

                        0b00_001100 => {
                            // SYSCALL
                            self.handle_syscall()?;
                        },
                        0b00_110100 => {
                            // TEQ
                            if self.gpr(instr.rs) == self.gpr(instr.rt) {
                                let code = (instr_val >> 6) & 0x000003ff;
                                return Err(VmExit::TrapException(
                                    VirtAddr(pc as usize), code));
                            }
                        },

                    
                    _ => unimplemented!("R {:#x?} @ pc {:#x?}", instr, pc),
                    

                    }

                
                },

                0b00_001111 => {
                    // LUI
                    let instr = IFormat::from(instr);
                    if instr.rs != 0 {
                        return Err(VmExit::IllegalInstruction(
                                VirtAddr(pc as usize)));
                    }

                   self.set_gpr(instr.rt, (instr.offset as u32) << 16); 
                },
                0b00_001001 => {
                    // ADDIU
                    let instr = IFormat::from(instr);
                    let im = instr.offset as i16 as i32 as u32;
                    let s =  self.gpr(instr.rs).wrapping_add(im);
                    self.set_gpr(instr.rt,s);
                },
                0b00_001100 => {
                    // ANDI
                    let instr = IFormat::from(instr);
                    let im = instr.offset as u32;
                    self.set_gpr(instr.rt, im & self.gpr(instr.rs));
                },
                0b00_001101 => {
                    // ORI
                    let instr = IFormat::from(instr);
                    let im = instr.offset as u32;
                    self.set_gpr(instr.rt, im | self.gpr(instr.rs));
                },
                0b00_001110 => {
                    // XORI
                    let instr = IFormat::from(instr);
                    let im = instr.offset as u32;
                    self.set_gpr(instr.rt, im ^ self.gpr(instr.rs));
                },

                // Loads and stores
                0b00_100011 => {
                    // LW
                    let instr = IFormat::from(instr);
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr = self.gpr(instr.rs).wrapping_add(off);
                    let naddr = self.gpr(instr.rt).wrapping_add(off);
                    //println!("b= {:#x} off= {:#x}", base, off);
                    //println!("about to read {:#x}", addr);
                    let v = self.mem.read_u32_le(VirtAddr(addr as usize))?;
                    
                    self.set_gpr(instr.rt, v);
                },
                0b00_110000 => {
                    // LL
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    //atomic_update = true;
                    let addr = self.gpr(base).wrapping_add(off);
                    let v = self.mem.read_u32_le(VirtAddr(addr as usize))?;
                    self.set_gpr(instr.rt, v); 
                },
                0b00_111000 => {
                    // SC
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr  = self.gpr(base).wrapping_add(off) as usize;
                    
                    //if atomic_update == true {
                        self.mem.write_u32_le(
                            VirtAddr(addr), self.gpr(instr.rt))?;
                        self.set_gpr(instr.rt, 1);
                        //atomic_update = false;
                    //} else {
                    //    self.set_gpr(instr.rt, 0);
                    //}
                },
                 0b00_101011 => {
                    // SW
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr  = self.gpr(base).wrapping_add(off) as usize;
                    self.mem.write_u32_le(VirtAddr(addr), self.gpr(instr.rt))?;    
                },

                0b00_101000 => {
                    // SB
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr  = self.gpr(base).wrapping_add(off) as usize;
                    
                    self.mem.write_u8_le(VirtAddr(addr), 
                                         self.gpr(instr.rt) as u8)?;
                },
                0b00_101001 => {
                    // SH
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr  = self.gpr(base).wrapping_add(off) as usize;
                    
                    self.mem.write_u16_le(VirtAddr(addr), 
                                         self.gpr(instr.rt) as u16)?;
                },

                0b00_100000 => {
                    // LB
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr = self.gpr(base).wrapping_add(off) as usize;
                    let v = self.mem.read_u8_le(VirtAddr(addr))? as i8 as i32;
                    self.set_gpr(instr.rt, v as u32);

                },
                0b00_100100 => {
                    // LBU
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr = self.gpr(base).wrapping_add(off) as usize;
                    let v = self.mem.read_u8_le(VirtAddr(addr))? as u32;
                    self.set_gpr(instr.rt, v as u32);

                },

                0b00_100010 => {
                    // LWL
                    let instr = IFormat::from(instr);
                    let effaddr = self.gpr(instr.rs).wrapping_add(
                        instr.offset as i16 as i32 as u32);
                    //panic!("LWL effaddr: {:#x}", effaddr);
                    let w = self.mem.read_u32_le(VirtAddr((effaddr & 0xfffffffc) 
                                                          as usize))?;
                    let s = ((!effaddr)&3) << 3;
                    self.set_gpr(instr.rt, 
                                 (self.gpr(instr.rt) & 0x0000ffff) | (w << s));
                    
                    //panic!("LWL result rt:{:#x}", self.gpr(instr.rt));
                },
                0b00_100110 => {
                    // LWR
                    let instr = IFormat::from(instr);
                    let effaddr = self.gpr(instr.rs).wrapping_add(
                        instr.offset as i16 as i32 as u32);
                    let w = self.mem.read_u32_le(VirtAddr((effaddr & 0xfffffffc) 
                                                          as usize))?;
                    let s = (effaddr&3) << 3;
                    self.set_gpr(instr.rt, 
                                 (self.gpr(instr.rt) & 0xffff0000) | (w >> s));
                
                
                    //panic!("LWR result rt:{:#x}", self.gpr(instr.rt));
                },
                 0b00_101010 => {
                    // SWL
                    unimplemented!();
                    let instr = IFormat::from(instr);
                    let effaddr = self.gpr(instr.rs).wrapping_add(
                        instr.offset as i16 as i32 as u32);
                    
                    /*let w = self.mem.read_u32_le(VirtAddr(
                            (effaddr & 0xfffffffc) as usize))?;

                    let o = effaddr & 3;
                    let mut v = w;
                    match o {
                        0 => { //
                            v = (w & 0xffffff00) | (self.gpr(instr.rt) & 0x00ffffff);
                        },
                        1 => {
                            v = (w & 0xffff0000) | (self.gpr(instr.rt) & 0x0000ffff);
                        },
                        2 => {
                            v = (w & 0xff000000) | (self.gpr(instr.rt) & 0x00ffffff);
                        },
                        3 => {
                            // v = w; it already is.
                        },
                        _ => unreachable!(),
                    };
                 
                    self.mem.write_u32_le(VirtAddr((effaddr & 0xfffffffc) as usize), v); 
                */
                // IMPORTANT: TODO: XXX:
                // THIS ASSUMES THAT THE HOST MACHINE IS LITTLE ENDIAN, JUST LIKE
                // THE GUEST.
                /*let sl = unsafe {
                    core::slice::from_raw_parts(self.gpr(instr.rt) 
                                                as &u32 as *const u32 as *const u8,
                                                )
                };*/
                },
                0b00_101110 => {
                    unimplemented!();
                    // SWR
                    let instr = IFormat::from(instr);
                    let effaddr = self.gpr(instr.rs).wrapping_add(
                        instr.offset as i16 as i32 as u32);
                    
                    let w = self.mem.read_u32_le(VirtAddr(
                            (effaddr & 0xfffffffc) as usize))?;

                    let o = effaddr & 3;
                    let mut v = w;
                    match o {
                        0 => {
                            // v = w; it already is.
                        },
                        1 => {
                            v = (w & 0x000000ff) | (self.gpr(instr.rt) & 0xffffff00);
                        },
                        2 => {
                            v = (w & 0x0000ffff) | (self.gpr(instr.rt) & 0xffff0000);
                        },
                        3 => {
                            v = (w & 0x00ffffff) | (self.gpr(instr.rt) & 0xff000000);
                        },
                        _ => unreachable!(),
                 };
                 
                 self.mem.write_u32_le(VirtAddr((effaddr & 0xfffffffc) as usize), v);
                },

                //0b00_

                0b00_100101 => {
                    // LHU
                    let instr = IFormat::from(instr);

                    let ea = (instr_val & 0xffff).wrapping_add(self.gpr(instr.rs));
                    let v = self.mem.read_u16_le(VirtAddr(ea as usize))? as u32;
                    self.set_gpr(instr.rt, v);

                },

                0b00_000111 => {
                    // BGTZ
                    let instr = IFormat::from(instr);
                    if self.gpr(instr.rs) as i32 > 0 {
                        let toff = (instr.offset as i16 as i32) << 2;
                        let target_pc = (toff as u32)
                                    .wrapping_add(self.pc()+4);

                        jmp_target = Some(target_pc);
                        self.set_pc(pc.wrapping_add(4));
                        continue 'next_instr;
                    }
                }, 
                0b00_000001 => {
                    // regimm
                    let instr_val = instr;
                    let instr = IFormat::from(instr);
                    
                    match instr.rt {
                        0b000_00000 => {
                            // BLTZ
                            if (self.gpr(instr.rs) as i32) < 0 {
                                let toff = (instr.offset as i16 as i32) << 2;
                                let target_pc = (toff as u32)
                                            .wrapping_add(self.pc()+4);

                                jmp_target = Some(target_pc);
                                self.set_pc(pc.wrapping_add(4));
                                continue 'next_instr;
                            }
                        },
                        0b000_00001 => {
                            // BGEZ
                            if self.gpr(instr.rs) as i32 >= 0 {
                                let toff = (instr.offset as i16 as i32) << 2;
                                let target_pc = (toff as u32)
                                            .wrapping_add(self.pc()+4);

                                jmp_target = Some(target_pc);
                                self.set_pc(pc.wrapping_add(4));
                                continue 'next_instr;
                            }

                        },
                        0b000_10001 => {
                            // BGEZAL
                            if self.gpr(instr.rs) as i32 >= 0 {
                                let toff = (instr.offset as i16 as i32 as u32) << 2;
                                let target_pc = (toff as u32)
                                            .wrapping_add(self.pc()+4);
                                
                                self.set_gpr(31, pc.wrapping_add(8));
                                
                                jmp_target = Some(target_pc);
                                //println!("DEBUG link to pc {:#x}", target_pc);
                                self.set_pc(pc.wrapping_add(4));
                                continue 'next_instr;
                            }

                        },
                        
                        x => unimplemented!("pepito perez {:#x}
                                            @ pc {:x}", instr_val, pc),
                    }
                },
                0b00_000110 => {
                    // BLEZ
                    let instr = IFormat::from(instr);
                    if instr.rt != 0 {
                        return Err(VmExit::IllegalInstruction(
                            VirtAddr(pc as usize)));
                    
                    }
                    
                    if self.gpr(instr.rs) as i32 <= 0 {
                        let toff = (instr.offset as i16 as i32) << 2;
                        let target_pc = (toff as u32)
                                    .wrapping_add(self.pc()+4);

                        jmp_target = Some(target_pc);
                        self.set_pc(pc.wrapping_add(4));
                        continue 'next_instr;
                    }
                },

                0b00_001011 => {
                    // SLTIU
                    let instr = IFormat::from(instr);
                    let imm = instr.offset as i16 as i32 as u32;
                    if self.gpr(instr.rs) < imm {
                        self.set_gpr(instr.rt, 1);
                    } else {
                        self.set_gpr(instr.rt, 0);
                    }
                },
                0b00_001010 => {
                    // SLTI
                    let instr = IFormat::from(instr);
                    let imm = instr.offset as i16 as i32;
                    if (self.gpr(instr.rs) as i32) < imm {
                        self.set_gpr(instr.rt, 1);
                    } else {
                        self.set_gpr(instr.rt, 0);
                    }
                },

                _ => unimplemented!("{:#x?} @ pc {:#x?}", instr, pc),
            
            
            } // end op match.
            
            let next_pc = match jmp_target {
                None => pc.wrapping_add(4),
                Some(val) => {
                    jmp_target = None;
                    val
                }
            };
            /*println!("PC:{:#08x}", pc);
            for (i,r) in self.GPR.iter().enumerate() {
                    println!("R#{:?}:\t\t{:08x}", i, r);
            }*/
            self.set_pc(next_pc);

        } // end 'next_instr loop.
    }

// https://git.linux-mips.org/cgit/ralf/linux.git/tree/arch/mips/include/uapi/asm/unistd.h
// https://www.linux-mips.org/wiki/Syscall
// Remeber to set reguster A3 to 0 on success and 1 on failure.
    fn handle_syscall(&mut self) -> Result<(), VmExit> {
        let nr: u32 = self.gpr(GReg::V0 as usize);
        
        match nr {
            4049 => {
                // __NR_geteuid
                println!("sys_geteuid()");
                self.set_gpr(GReg::V0 as usize, 0); // return root UID (0)
                self.set_gpr(GReg::A3 as usize, 0);
            },
            4024 => {
                // __NR_getuid
                println!("sys_getuid()");
                self.set_gpr(GReg::V0 as usize, 0); // return root UID (0)
                self.set_gpr(GReg::A3 as usize, 0);
            },
            4050 => {
                // __NR_getegid
                println!("sys_getegid()");
                self.set_gpr(GReg::V0 as usize, 0); // return root GID (0)
                self.set_gpr(GReg::A3 as usize, 0);
            },
            4047 => {
                // __NR_getgid
                println!("sys_getgid()");
                self.set_gpr(GReg::V0 as usize, 0); // return root UID (0)
                self.set_gpr(GReg::A3 as usize, 0);
            },

            4045 => {
                // __NR_brk
                println!("sys_brk() a0: {:#x}", self.gpr(GReg::A0 as usize));
                
                let addr = self.gpr(GReg::A0 as usize) as usize;
                let res = self.mem.brk(VirtAddr(addr));
                

                let res = res.ok_or(VmExit::SegmentOverflow)?;

                self.set_gpr(GReg::V0 as usize, res as u32);
                self.set_gpr(GReg::A3 as usize, 0);
            },

            4283 => {
                // __NR_set_thread_area
                println!("sys_set_thread_area({:#x})", self.gpr(GReg::A0 as usize)); 
                self.CP0_UserLocal = self.gpr(GReg::A0 as usize);
                self.set_gpr(GReg::V0 as usize, 0);
                self.set_gpr(GReg::A3 as usize, 0);
                //panic!("CP0_UserLocal = {:#x}", self.CP0_UserLocal);
            },

            4288 => {
                // __NR_openat
                unimplemented!("sys_openat()");
                /*let arg0 = self.gpr(GReg::A0 as usize) as usize as isize;
                let arg1 = self.gpr(GReg::A1 as usize) as usize;

                println!(" openat arg0={:?} arg1={:#x}", arg0, arg1);
                let mut buf = [0u8; 64];
                self.mem.read(VirtAddr(arg1), &mut buf).unwrap();
                println!("[{:?}]", std::str::from_utf8(&buf));
                self.set_gpr(GReg::V0 as usize, 3);
                self.set_gpr(GReg::A3 as usize, 0);*/
                

            },
            4006 => {
                // __NR_close
                unimplemented!("sys_close()");
                /*self.set_gpr(GReg::A3 as usize, 0);
                self.set_gpr(GReg::V0 as usize, 0);*/
            },

            4146 => {
                // __NR_writev
                //unimplemented!("sys_writev()");

                // debug version so far, it paics.
                let arg0 = self.gpr(GReg::A0 as usize) as usize;
                let arg1 = self.gpr(GReg::A1 as usize) as usize;
                
                let a = self.mem.read_u32_le(VirtAddr(arg1)).unwrap() as usize;
                let l = self.mem.read_u32_le(VirtAddr(arg1+4)).unwrap() as usize;
                let mut buf = vec![0u8; l];
                self.mem.read(VirtAddr(a), &mut buf).unwrap();
                
                self.set_gpr(GReg::A3 as usize, 0);
                self.set_gpr(GReg::V0 as usize, l as u32);
                
                panic!("!!!!!!!! writev arg0 {:?},,,, buf:[{:?}]",
                       arg0, std::str::from_utf8(&buf));
            },

            4122 => {
                // __NR_uname TODO improve this
                println!("sys_uname()");
                let user_buf = self.gpr(GReg::A0 as usize); // arg0

// https://elixir.bootlin.com/linux/latest/source/include/uapi/linux/utsname.h#L17
                let mut d = vec![0u8; 65*5];
                &d[0..6].copy_from_slice(b"Linux\x00");
                &d[65..65+5].copy_from_slice(b"node\x00");
                &d[65*2..(65*2)+6].copy_from_slice(b"3.2.0\x00");
                

                self.mem.write(VirtAddr(user_buf as usize), &d[..]);

                self.set_gpr(GReg::V0 as usize, 0);
                self.set_gpr(GReg::A3 as usize, 0); // success
            },


            4003 => {
                // __NR_read 
                panic!("sys_read()");
                /*let arg0 = self.gpr(GReg::A0 as usize) as usize;
                let arg1 = self.gpr(GReg::A1 as usize) as usize;
                let arg2 = self.gpr(GReg::A2 as usize) as usize;
                //panic!();
                if arg0 != 3 {
                    panic!("sys_read() arg0: {:?}", arg0);
                }
                panic!("read 3");
                
                //panic!("arg1: {:?} arg2: {:?}", arg1, arg2);
                let ks = b"5.4.0-48-generic";
                self.mem.write(VirtAddr(arg1), &ks[..]);
                
                self.set_gpr(GReg::V0 as usize, 0); // EOF
                self.set_gpr(GReg::A3 as usize, 0); // syscall success*/

            },

            4004 => {
                // __NR_write
                let fd    = self.gpr(GReg::A0 as usize);
                let buf   = self.gpr(GReg::A1 as usize);
                let count = self.gpr(GReg::A2 as usize);
                if fd != 1 {
                    unimplemented!("sys_write(): can only write to fd 1. {:?}",
                        fd);
                }
                
                println!("sys_write(): wrote {:?} bytes from {:#x} to fd {:?} @ pc ?",
                         count, buf, fd);

                self.set_gpr(GReg::V0 as usize, count);
                self.set_gpr(GReg::A3 as usize, 0);
                
                // test
                let mut tmpbuf = vec![0u8; count as usize];
                self.mem.read(VirtAddr(buf as usize), &mut tmpbuf[..]);
                println!("data: [{:?}]", &tmpbuf);
                
            },

            4085 => {
                // __NR_readlink
                let arg0 = self.gpr(GReg::A0 as usize) as usize;
                let arg1 = self.gpr(GReg::A1 as usize) as usize;
                
                let mut buf = [0u8; 14];
                self.mem.read(VirtAddr(arg0), &mut buf).unwrap();
                println!("readlink [{:?}]", std::str::from_utf8(&buf));
                if buf != *b"/proc/self/exe" {
                    panic!("readlink not fully implemented.");
                } 
                let sl = b"/usr/bin/readlink\x00";
                self.mem.write(VirtAddr(arg1), &sl[..]);

                self.set_gpr(GReg::V0 as usize, sl.len() as u32);
                self.set_gpr(GReg::A3 as usize, 0);      
            },
            
            4215 => {
                // __NR_fstat64
/*  
The returned buf is this struct:
https://elixir.bootlin.com/linux/latest/source/arch/mips/include/uapi/asm/stat.h#L52

Here is a dump of the statbuf returned by the emulated kernel in qemu
when calling sys_fstat64() with fd=1, which is what libc does before calling main:
(gdb) x/104bx 0x407ffa18
0x407ffa18:	0x17	0x00	0x00	0x00	0x00	0x00	0x00	0x00
0x407ffa20:	0x00	0x00	0x00	0x00	0x00	0x00	0x00	0x00
0x407ffa28:	0x09	0x00	0x00	0x00	0x00	0x00	0x00	0x00
0x407ffa30:	0x90	0x21	0x00	0x00	0x01	0x00	0x00	0x00
0x407ffa38:	0xe8	0x03	0x00	0x00	0x05	0x00	0x00	0x00
0x407ffa40:	0x06	0x88	0x00	0x00	0x00	0x00	0x00	0x00
0x407ffa48:	0x00	0x00	0x00	0x00	0x00	0x00	0x00	0x00
0x407ffa50:	0x00	0x00	0x00	0x00	0x00	0x00	0x00	0x00
0x407ffa58:	0x2f	0x13	0x77	0x5f	0x6b	0x8e	0x4b	0x26
0x407ffa60:	0x2f	0x13	0x77	0x5f	0x6b	0x8e	0x4b	0x26
0x407ffa68:	0x85	0x0d	0x77	0x5f	0x6b	0x8e	0x4b	0x26
0x407ffa70:	0x00	0x04	0x00	0x00	0x00	0x00	0x00	0x00
0x407ffa78:	0x00	0x00	0x00	0x00	0x00	0x00	0x00	0x00

 * ALSO, V0 and A3 are set to zero.
 * */
                //panic!("fd: {:?}", self.gpr(GReg::A0 as usize));
                println!("__NR_fstat64 fd:{:?}", self.gpr(GReg::A0 as usize));
                
                if self.gpr(GReg::A0 as usize) != 1 {
                    panic!("fstat only implemented for fd 1.");
                }

                let mut stat  = Stat64::default();
                stat.st_dev     = 0x17;
                stat.st_ino     = 0x09;
                stat.st_mode    = 0x00002190;
                stat.st_nlink   = 1;
                stat.st_rdev    = 0x00008806;
                stat.st_size    = 0;
                /* st_atime, st_atime_nsec ... we let them to zero idk. */
                stat.st_blksize = 0;
                stat.st_blocks  = 0;

                //let zeroes = vec![0u8; 26*4];
                let stat_buf = unsafe {
                    core::slice::from_raw_parts(&stat as *const Stat64 as *const u8,
                                                core::mem::size_of_val(&stat))
                };
                let addr = self.gpr(GReg::A1 as usize) as usize;
                self.mem.write(VirtAddr(addr), &stat_buf[..]).unwrap();

                self.set_gpr(GReg::V0 as usize, 0);
                self.set_gpr(GReg::A3 as usize, 0);
            },

            4246 => {
                // __NR_exit_group
                let status = self.gpr(GReg::A0 as usize) as i32;
                return Err(VmExit::Finish(status));

            }, 

            1337 => {
                // Debug syscall (not present in Linux).
                // When called prints the registers on host's terminal
                // and terminates the vm.
                for (i,r) in self.GPR.iter().enumerate() {
                    println!("R#{:?}:\t\t{:08x}", i, r);
                }
                return Err(VmExit::ExecFault(VirtAddr(0x13371337)));
            }


            _ => {
                unimplemented!("SYSCALL nr: {:?}", nr);
            },
        }
        

        Ok(())
    }

    /// Map the main ELF binary from a file into the guest.
    /// Returns an `Err` with an opaque error number on failure.
    /// On succes, pc is set to entry point. On error pc is not touched.
    pub fn map_elf(&mut self, path: &Path) -> Result<(), i32> {
        // Read the main elf into a Vec<u8>
        let bin = std::fs::read(path).or(Err(1))?;

        // Check headers
        // Check ELF MAGIC
        if bin.get(0..4) != Some(b"\x7fELF") {
            return Err(2);
        }
        // Check EI_CLASS (ELFCLASS32).
        if bin.get(4) != Some(&(0x01 as u8)) {
            return Err(3);
        }
        // Check EI_DATA (ELFDATA2LSB)
        if bin.get(5) != Some(&(0x01 as u8)) {
            return Err(3);
        }
        // Checking EI_VERSION (EV_CURRENT)
        if bin.get(6) != Some(&(0x01 as u8)) {
            return Err(4);
        }
        // Checking EI_OSABI (ELFOSABI_SYSV)
        if bin.get(7) != Some(&(0x00 as u8)) {
             return Err(5);
        }
        // Checking EI_OSABI (1) maybe accept 0?
        /*if bin.get(8) != Some(&(0x01 as u8)) {
             return Err(6);
        }*/
        // Now we can assume offsets into the file.
        
        // TODO: Check e_machine and e_flags. Not critical.
        // TODO: Check whether it's pie or not and realloc base. Also
        // check it is not dynamically linked.
       
        // These lambdas are for reading an int from the Vec<u8> in little endian.
        // Fails with Err(()) if out-of-bounds.
        let read_u32_le = |b: &[u8], i: usize| -> Result<u32, ()> {
            use std::convert::TryInto;
            Ok(u32::from_le_bytes(b.get(i .. i+4).ok_or(())?.try_into()
                .unwrap()))
        };
    
        let read_u16_le = |b: &[u8], i: usize| -> Result<u16, ()> {
            use std::convert::TryInto;
            Ok(u16::from_le_bytes(b.get(i .. i+2).ok_or(())?.try_into()
                .unwrap()))
        };
    

        // Read program header offset.
        let ph_off = read_u32_le(&bin, 0x1c).or(Err(7))?;
        
        // Read the number of program headers.
        let ph_num = read_u16_le(&bin, 0x2c ).or(Err(8))?;
        if  ph_num == 0 || ph_num > 512 { return Err(9); }

        // Read the ph entry size and check
        let ph_entsize = read_u16_le(&bin, 0x2a).or(Err(10))?;
        if(ph_entsize != 32) { return Err(11) }
        
        // Get a slice into the program header bytes and check bounds.
        let phs_bytes = bin.get(
            ph_off as usize .. 
            ph_off as usize + (ph_num as usize).checked_mul(ph_entsize as usize)
            .ok_or(24)?
        ).ok_or(25)?;
        
        
        // Iterate over each segment. Ignore non-PT_LOADs and map the
        // PT_LOAD segment. Collect the end of the last PT_LOAD segment
        // so we can set data_end and brk.
        let mut data_end: Option<usize> = None;
        let phs = phs_bytes.chunks(ph_entsize as usize);
        for ph in phs {
            if read_u32_le(ph, 0).or(Err(12))? != 1 {
                continue; // skipping non PT_LOAD segments.
            }

            let of  = read_u32_le(ph, 4 ).or(Err(13))? as usize;   // Offset
            let va  = read_u32_le(ph, 8 ).or(Err(14))? as usize;   // VirtAddr
            let fz  = read_u32_le(ph, 16).or(Err(15))? as usize;   // FileSiz
            let mz  = read_u32_le(ph, 20).or(Err(16))? as usize;   // MemSiz
            let flg = read_u32_le(ph, 24).or(Err(17))?;            // Flg
            
            let mut perms = Perm(PERM_RAW); // initialized
            if (flg & 0x1) != 0 { perms.0 |= PERM_EXEC };
            if (flg & 0x2) != 0 { perms.0 |= PERM_WRITE };
            if (flg & 0x4) != 0 { perms.0 |= PERM_READ };
            
            // Load the segment and reserve .bss space if needed.
            let seg_bytes = bin.get(of .. 
                             of.checked_add(std::cmp::min(fz, mz))
                            .ok_or(22)?).ok_or(23)?;
        
            self.mem.write_ignore_perms(VirtAddr(va), seg_bytes)
                .or(Err(18))?;
            self.mem.add_perms(VirtAddr(va), seg_bytes.len(), perms)
                .unwrap();
            
            // If MemSiz is greater than FileSiz, then we need to set to zero
            // those bytes, this is the .bss section or uninitialized data.
            // We don't need to align it, the compiler does that by setting
            // the appropiate size.
            
            if fz < mz {
                // XXX Refactor to fill with zeroes in a more efficient way (?)
                let zeroes = vec![0u8; mz - fz];
                self.mem.write_ignore_perms(VirtAddr(va.checked_add(fz)
                                                  .ok_or(19)?
                                        ), &zeroes).or(Err(20))?;

                // We set the .bss as readable and writable but non-executable.
                self.mem.add_perms(VirtAddr(va + fz), zeroes.len(),
                    perms).or(Err(21))?;
            }

            data_end = Some(va + mz);
        }
        
        match data_end {
            Some(v) => self.mem.data_end = v,
            None => return Err(30),
        }
        self.mem.brk = self.mem.data_end;

        // Get the entry point.
        let e_entry: u32 = read_u32_le(&bin, 0x18).or(Err(26))?;

        // Set the program counter to the entry point.
        self.set_pc(e_entry);


        Ok(())
    }
}
