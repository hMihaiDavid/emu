use std::path::Path;

use crate::vm_mem::{Mem, VirtAddr, Perm, PERM_READ, PERM_WRITE, PERM_EXEC,
                    PERM_RAW};

//// General purpose register indeces used to index `Vm::gprs`.
#[repr(usize)]
//#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GReg {
    Zero  = 0,
    At,
    V0,
    V1,
    A0,
    A1,
    A2,
    A3,
    T0,
    T1,
    T2,
    T3,
    T4,
    T5,
    T6,
    T7,
    S0,
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    T8,
    T9,
    K0,
    K1,
    Gp,
    Sp,
    S8, // aka fp, stack frame pointer or subroutine variable.
    Ra,
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

    /// Collision between data segment and stack segment. This happens
    /// because of brk() or when growing stack.
    SegmentOverflow,
}

// A linux SysV abi MIPS II LE emulated guest.
pub struct Vm {
    pub GPR:  [u32; 32],
    pub HI:   u32,
    pub LO:   u32,
    pub Pc:   u32,
    pub mem:  Mem, 
}

impl Vm {
    pub fn new(mem_size: usize) -> Self {
        assert!(mem_size != 0);
        Vm { // TODO implement trait Default
            GPR:  [0; 32],
            HI:   0u32,
            LO:   0u32,
            Pc:   0u32, // TODO CHECK proper initial state.
            mem:   Mem::new(mem_size),
        }
    }
    
    /// Returns a new `Vm` wihch has a shallow copy of `self`'s state but
    /// with the memory marked as non-dirty. You can call `reset()` on the
    /// returned `Vm` and it will be differentially restored to the state
    /// when the fork happened.
    pub fn fork(&self) -> Vm {
        Vm {
            GPR: self.GPR.clone(),
            HI:  self.HI.clone(),
            LO:  self.LO.clone(),
            Pc:  self.Pc.clone(),

            mem: self.mem.fork(),
        }
    }
    
    pub fn reset(&mut self, prev: &Vm) -> () {
        self.GPR = prev.GPR;
        self.HI  = prev.HI;
        self.LO  = prev.LO;
        self.Pc  = prev.Pc;

        self.mem.reset(&prev.mem);
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

            let instr_val = instr;
            
            println!("Executing instruction {:x} @ pc {:#x}", instr_val, pc);
            match (instr >> 26) as u8 { // higher 6 bits or op.
                0b00_110011 => {
                    // PREF
                    // Do nothing.
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
                            if instr.shamt != 0b000_11000 {
                                unimplemented!("BSHFL");
                            }
                            // SEH
                            let v = self.gpr(instr.rt) as u16 as i16 as i32;
                            self.set_gpr(instr.rd, v as u32);
                        },
                    _ => unimplemented!("SPECIAL3")
                    }
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
                    self.set_pc(pc.wrapping_add(4));
                    continue 'next_instr;
                },
                0b00_000100 => {
                    // BEQ
                    let instr = IFormat::from(instr);
                    
                    if(self.gpr(instr.rs) == self.gpr(instr.rt)) {
                        //println!("BEQ gpr(rs): {:#x} gpr(rt): {:#x}",
                        //self.gpr(instr.rs), self.gpr(instr.rt));

                        let mut ta = ((instr_val & 0x0000ffff) << 2) 
                            as u16 as i16 as i32 as u32;
                        ta = ta.wrapping_add(pc+4);
                        //println!("ta: {:#x}", ta);
                        jmp_target = Some(ta);
                        self.set_pc(pc.wrapping_add(4));
                        continue 'next_instr;
                    }
                },
                0b00_000101 => {
                    // BNEQ
                    let instr = IFormat::from(instr);
                    
                    if(self.gpr(instr.rs) != self.gpr(instr.rt)) {
                        //println!("BEQ gpr(rs): {:#x} gpr(rt): {:#x}",
                        //self.gpr(instr.rs), self.gpr(instr.rt));

                        let mut ta = ((instr_val & 0x0000ffff) << 2) 
                            as u16 as i16 as i32 as u32;
                        ta = ta.wrapping_add(pc+4);
                        //println!("ta: {:#x}", ta);
                        jmp_target = Some(ta);
                        self.set_pc(pc.wrapping_add(4));
                        continue 'next_instr;
                    }
                },



                0b00_000000 => { // R-format (higher 6 bits (op) to zero)
                    let instr = RFormat::from(instr);

                    match (instr.funct) as u8 {
                        0b00_000000 => {
                            // SLL
                            //panic!("la vie en rose");
                            if instr.rs != 0 {
                                return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }

                            self.set_gpr(instr.rd,
                                         self.gpr(instr.rt) << instr.shamt);
                        },
                        0b00_100101 => {
                            // OR
                            let res = self.gpr(instr.rs) | self.gpr(instr.rt);
                            self.set_gpr(instr.rd, res);
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
                        0b00_010010 => {
                            // MFLO
                            if instr.shamt != 0 || instr.rs != 0
                                || instr.rt != 0 {
                                    return Err(VmExit::IllegalInstruction(
                                            VirtAddr(pc as usize)));
                            }
                            self.set_gpr(instr.rd, self.LO);


                        }, 

                        0b00_101011 => {
                            // SLTU
                            if instr.shamt != 0 {
                                return Err(VmExit::IllegalInstruction(
                                        VirtAddr(pc as usize)));
                            }

                            if self.gpr(instr.rs) < self.gpr(instr.rt) {
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
                    self.set_gpr(instr.rt, self.gpr(instr.rs).wrapping_add(im));
                    //println!("CCCCC ADDIU im: {:#x}, gpr(instr.rs): {:#x}", im, self.gpr(instr.rs));
                    //println!("gpr(instr.rt) {:#x}", self.gpr(GReg::Sp as usize));
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

                // Loads and stores
                0b00_100011 => {
                    // LW
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr = self.gpr(base).wrapping_add(off);
                    //println!("b= {:#x} off= {:#x}", base, off);
                    //println!("about to read {:#x}", addr);
                    let v = self.mem.read_u32_le(VirtAddr(addr as usize))?;
                    //println!("read {:#x} from addr {:#x}", v, addr);
                    self.set_gpr(instr.rt, v);
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
                0b00_100000 => {
                    // LB
                    let instr = IFormat::from(instr);
                    let base  = instr.rs;
                    let off   = instr.offset as i16 as i32 as u32; 
                    
                    let addr = self.gpr(base).wrapping_add(off) as usize;
                    let v = self.mem.read_u8_le(VirtAddr(addr))? as i8 as i32;
                    self.set_gpr(instr.rt, v as u32);

                }


                0b00_100101 => {
                    // LHU
                    let instr = IFormat::from(instr);

                    let ea = (instr_val & 0xffff).wrapping_add(self.gpr(instr.rs));
                    let v = self.mem.read_u16_le(VirtAddr(ea as usize))? as u32;
                    self.set_gpr(instr.rt, v);

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
                                            .wrapping_add(self.pc());

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
                                            .wrapping_add(self.pc());

                                jmp_target = Some(target_pc);
                                self.set_pc(pc.wrapping_add(4));
                                continue 'next_instr;
                            }

                        },
                        0b000_10001 => {
                            // BGEZAL
                            if self.gpr(instr.rs) as i32 >= 0 {
                                let toff = (instr.offset as i16 as i32) << 2;
                                let target_pc = (toff as u32)
                                            .wrapping_add(self.pc());
                                
                                self.set_gpr(31, pc.wrapping_add(8));
                                
                                jmp_target = Some(target_pc);
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
                                    .wrapping_add(self.pc());

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
            self.set_pc(next_pc); 

        } // end 'next_instr loop.
    }

// https://git.linux-mips.org/cgit/ralf/linux.git/tree/arch/mips/include/uapi/asm/unistd.h
// https://www.linux-mips.org/wiki/Syscall
    fn handle_syscall(&mut self) -> Result<(), VmExit> {
        let nr: u32 = self.gpr(GReg::V0 as usize);
        
        match nr {
            4049 => {
                // __NR_geteuid
                self.set_gpr(GReg::V0 as usize, 0); // return root UID (0)
            },
            4024 => {
                // __NR_getuid
                self.set_gpr(GReg::V0 as usize, 0); // return root UID (0)
            },
            4050 => {
                // __NR_getegid
                self.set_gpr(GReg::V0 as usize, 0); // return root GID (0)
            },
            4047 => {
                // __NR_getgid
                self.set_gpr(GReg::V0 as usize, 0); // return root UID (0)
            },

            4045 => {
                // __NR_brk
                println!("BRK a0: {:?} a1: {:?}", self.gpr(GReg::A0 as usize),
                self.gpr(GReg::A1 as usize));
                
                let addr = self.gpr(GReg::A0 as usize) as usize;
                let res = self.mem.brk(VirtAddr(addr));
                let res = res.ok_or(VmExit::SegmentOverflow)?;

                self.set_gpr(GReg::V0 as usize, res as u32);

            },

            4283 => {
                // __NR_set_thread_area
                // From man SET_THREAD_AREA(2):
                // "On MIPS and m68k, set_thread_area() always returns 0."
                // Nice!
                self.set_gpr(GReg::V0 as usize, 0);
            },

            4288 => {
                // __NR_openat
                let arg1 = self.gpr(GReg::A1 as usize) as usize;

                println!("------------ {:#x}", arg1);
                let mut buf = [0u8; 64];
                self.mem.read(VirtAddr(arg1), &mut buf).unwrap();
                println!("[{:?}]", std::str::from_utf8(&buf));
                
                self.set_gpr(GReg::V0 as usize, !0);
                //panic!("ALDI");
            },

            4146 => {
                // __NR_writev
                let arg0 = self.gpr(GReg::A0 as usize) as usize;
                let arg1 = self.gpr(GReg::A1 as usize) as usize;
                
                let a = self.mem.read_u32_le(VirtAddr(arg1)).unwrap() as usize;
                let mut buf = [0u8; 64];
                self.mem.read(VirtAddr(a), &mut buf).unwrap();
                
                
                panic!("!!!!!!!! writev arg0 {:?},,,, buf:[{:?}]",
                       arg0, std::str::from_utf8(&buf));
            },

            _ => {
                unimplemented!("SYSCALL nr: {:?}", nr);
            }
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
