use std::path::Path;

use crate::vm_mem::{Mem, VirtAddr, Perm, PERM_READ, PERM_WRITE, PERM_EXEC,
                    PERM_RAW };

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
            shamt: ( (inst >> 5) & 0x1f) as u8,      // next  5 bits
            rd   : ( (inst >> 11) & 0x1f) as usize,  // next  5 bits 
            rt   : ( (inst >> 16) & 0x1f) as usize,  // next  5 bits 
            rs   : ( (inst >> 21) & 0x1f) as usize,  // next  5 bits 
        }
    }
}

struct IFormat {
    // TODO    
}

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
    IllegalIstruction(VirtAddr),
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
        'next_instr: loop {
            let pc: u32    = self.pc();
            let instr: u32 = self.mem.read_u32_le_exec(VirtAddr(pc as usize))?;
            
            // Decode instrucion and execute its semantics.

            match (instr >> 26) as u8 { // higher 6 bits or op.
                0b00_000000 => { // R-format (higher 6 bits (op) to zero)
                    let instr = RFormat::from(instr);

                    match (instr.funct) as u8 {
                        0b00_100101 => {
                            // OR
                            let res = self.gpr(instr.rs) | self.gpr(instr.rt);
                            self.set_gpr(instr.rd, res);
                            panic!("BENITO KAMELAS")
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
                        }


                    _ => panic!("kek!"),
                    
                    }
                },
                _ => unimplemented!("{:x?} @ pc {:#x?}", instr, pc),
            }

            let pc = pc.wrapping_add(4);
            self.set_pc(pc);
        }
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
        if bin.get(8) != Some(&(0x01 as u8)) {
             return Err(6);
        }
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
        
        // Iterate over each program header and collect the info we need about
        // each PT_LOAD segment.

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
        }

        // Get the entry point.
        let e_entry: u32 = read_u32_le(&bin, 0x18).or(Err(26))?;

        // Set the program counter to the entry point.
        self.set_pc(e_entry);

        Ok(())
    }
}
