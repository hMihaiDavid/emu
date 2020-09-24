use crate::vm::{ VmExit };

use std::convert::TryInto;

/// Size of a dirty block.
pub const DIRTY_BLOCK_SZ: usize = 128;

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Perm(pub u8);

pub const PERM_NONE:  u8 = 1 << 0;
pub const PERM_READ:  u8 = 1 << 1;
pub const PERM_WRITE: u8 = 1 << 2;
pub const PERM_EXEC:  u8 = 1 << 3;

/// Uninitialized memory has this bit to 0 and it is set on writes. Used
/// to detect reads from uninitialized memory.
pub const PERM_RAW:   u8 = 1 << 5;

pub const PERM_ALL:   u8 = PERM_READ | PERM_WRITE | PERM_EXEC | PERM_RAW;

/// A guest virtual address.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirtAddr(pub usize);


/// A virtual memory space used by `Vm`.
pub struct Mem {
    /// The backing storage for the memory space.
    /// index zero corresponds to byte zero in the guest va space.
    pub mem: Vec<u8>,

    /// For each byte in `mem` there is a corresponding byte here at the same
    /// offset. It holds a bitse of `Perm`  byte-level permissions and 
    /// other metadata.
    pub perms: Vec<Perm>,
    
    /// A list of virtual addresses of the blocks that are dirty.
    /// The blocks are of size `DIRTY_BLOCK_SZ`. It is used to traverse
    /// dirty memory efficiently when doing a differential reset.
    dirty_blocks_list: Vec<usize>,
    
    /// There is one bit for each block of memory of size `DIRTY_BLOCK_SZ`.
    /// It is used to keep track of which dirty blocks have been added to
    /// the `dirty_blocks_list` so that a block is not added more than once.
    pub dirty_blocks_bmp: Vec<u8>,
    
    /// top of the stack.
    pub stack_top: usize,

    /// program break
    pub brk: usize,

    /// end of the last PT_LOAD segment of the ELF. This will be the initial
    /// program break. It is used so that decreasing program break doesn't 
    /// underflow.
    pub data_end: usize,
}

impl Mem {
    /// Create a new `Mem` with `size` bytes.
    /// Calling this with `size` 0 panics.
    pub fn new(size: usize) -> Self {
        assert!(size != 0);
        // Align size up to the next multiple of DIRTY_BLOCK_SZ
        // let size = (size + DIRTY_BLOCK_SZ - 1) & !(DIRTY_BLOCK_SZ - 1); 
        
        Mem {
            mem:    vec![0; size],
            perms:  vec![Perm(PERM_NONE); size],

            dirty_blocks_list: Vec::with_capacity( size / DIRTY_BLOCK_SZ + 1),
            dirty_blocks_bmp:   vec![0; size / DIRTY_BLOCK_SZ  / 8 + 1],
            
            // no stack initially. Call self.grow_stack() to increase stack.
            stack_top: size,

            
            // These two are properly initialized by load_elf. 0 is invalid.

            // End address of highest loaded elf segment. Never changes.
            data_end: 0usize,
            // Program break, initially set to data_end, will be changed
            // by calls to self.brk() UNIX style :)
            brk: 0usize,
            
        }
    }

    /// Returns a new `Mem` with the same contents and `perms` but with
    /// all memory marked as non-dirty.
    pub fn fork(&self) -> Mem {
        Mem {
            mem:    self.mem.clone(),
            perms:  self.perms.clone(),

            dirty_blocks_list: Vec::with_capacity(self.dirty_blocks_list
                                                  .capacity()),
            dirty_blocks_bmp:  vec![0x00; self.dirty_blocks_bmp.capacity()],
            
            stack_top: self.stack_top,

            brk: self.brk,
            data_end: self.data_end,
        }
    }

    pub fn reset(&mut self, prev: &Mem) -> () {
        // Restore the dirtied blockes of `mem` and `perms`.
        for block in &self.dirty_blocks_list {
            let block = *block;
            
            let a = block * DIRTY_BLOCK_SZ;
            let b = a + DIRTY_BLOCK_SZ;
            
            &self.mem[a .. b].copy_from_slice(&prev.mem[a .. b]);
            &self.perms[a .. b].copy_from_slice(&prev.perms[a .. b]);
        }

        self.dirty_blocks_list.clear();
        self.dirty_blocks_bmp.iter_mut().for_each(|x| *x=0); // calling clear()
                                                // here is a big bug!

        self.stack_top = prev.stack_top;
        self.brk = prev.brk;
        self.data_end = prev.data_end;
    }

    /// Grows the stack by the given amount.
    pub fn grow_stack(&mut self, amnt: usize) -> Result<VirtAddr, VmExit> {
        let nst = self.stack_top.checked_sub(amnt).
                                  ok_or(VmExit::AddrOverflow(VirtAddr(!0)))?;
        if(nst <= self.brk) { // TODO improve error reporting.
           return Err(VmExit::AddrOverflow(VirtAddr(!0)));
        }

        self.add_perms(VirtAddr(nst), self.stack_top - nst,
                       Perm(PERM_READ | PERM_WRITE));
        self.stack_top = nst;

        Ok(VirtAddr(nst)) // return the new stack top.
    }

    /// shrink the stack by the given amount.
    pub fn shrink_stack(&mut self, amnt: usize) -> Result<VirtAddr, VmExit> {
        let nst = self.stack_top.checked_add(amnt)
                    .ok_or(VmExit::AddrOverflow(VirtAddr(!0)))?;
        if nst >= self.mem.len() {
            return Err(VmExit::AddrOverflow(VirtAddr(!0)));
        }
        
        // Remove all perms
        self.remove_perms(VirtAddr(self.stack_top), nst - self.stack_top,
                                   Perm(!0));
        
        self.stack_top = nst;
        Ok(VirtAddr(nst))
    }
    
    pub fn brk(&mut self, addr: VirtAddr) -> Option<usize> {
        let addr = addr.0;

        if addr == 0 || addr == self.brk {
            return Some(self.brk);
        }

        // check collision with main binary and stack.
        if addr < self.data_end  || addr >= self.stack_top {
            return None;
        }
        
        // Set permissions of the increased or decreased region appropiately.
        if addr < self.brk {
            self.set_perms(VirtAddr(addr), self.brk-addr, Perm(0));    
        } else { // addr > self.brk  (because of equality check at the begining)
            self.set_perms(VirtAddr(self.brk), addr-self.brk,
                           Perm(PERM_READ | PERM_WRITE));
        }
        
        // Set the new brk and return it.
        self.brk = addr;
        Some(addr)
    } 
        

    /// Set as dirty the memory in the range [addr, addr+size).
    /// It can panic if out of bounds so make sure it is called 
    /// after bound checking is already performed.
    #[inline]
    fn set_dirty(&mut self, addr: VirtAddr, size: usize) -> () {
        if size == 0 { return }
        let addr = addr.0;
       
        let start = addr / DIRTY_BLOCK_SZ;
        let end   = ((addr + size)-1) / DIRTY_BLOCK_SZ;
        
        for block in start ..= end { 
            let off = block / 8;
            let idx = block % 8;
            
            if (self.dirty_blocks_bmp[off] & (1 << idx)) == 0 {
                // Mark the block as dirty.
                self.dirty_blocks_bmp[off] |= 1 << idx;
                // Add the base address of the block into the list of dirty blocks.
                self.dirty_blocks_list.push(block);
            }
        }
    }
    
    /// Reads guest memory from `addr` into `buf`
    /// without checking memory permissions. It does the necessary bound 
    /// checking. 
    pub fn read_ignore_perms(&self, addr: VirtAddr, buf: &mut [u8])
        -> Result<(), VmExit> {
        let sl = self.mem.get(
            addr.0 ..
            addr.0.checked_add(buf.len()).ok_or(VmExit::AddrOverflow(addr))?
        ).ok_or(VmExit::ReadFault(addr))?; // XXX: make addr more accurate :)
        
        // This won't panic cause bound checking is performed already.
        buf.copy_from_slice(sl);
        Ok(())
    }
    
    /// Writes `buf` into guest memory at address `addr`
    /// without checking memory permissions.
    /// It does not set the memory as initialized but it marks it as dirty.
    /// It does the necessary bound checking.
    pub fn write_ignore_perms(&mut self, addr: VirtAddr, buf: &[u8])
        -> Result<(), VmExit> {
        let sl = self.mem.get_mut(
            addr.0 ..
            addr.0.checked_add(buf.len()).ok_or(VmExit::AddrOverflow(addr))?
        ).ok_or(VmExit::WriteFault(addr))?;
        
        // This won't panic cause bound checking is performed already.
        sl.copy_from_slice(buf);
        
        // Set the memory as dirty
        self.set_dirty(addr, buf.len());    

        Ok(())
    }

    /// Check the necessary permissions for performing a read from within
    /// the vm. It returns the faulting reason in a `VmExit`.
    /// It performs the required bound checking and if it doesn't
    /// return an error it is safe to access the `Mem::mem` and `Mem::perms`
    /// buffers in the range [addr, addr+size) without faulting in any way
    /// or overflowing the addition `addr+size` (this condition is checked for).
    pub fn check_perms_read(&self, addr: VirtAddr, size: usize)
        -> Result<(), VmExit> {
        // Get a slice to the required permissions and check for bounds
        let psl = self.perms.get(
            addr.0 ..
            addr.0.checked_add(size).ok_or(VmExit::AddrOverflow(addr))?
            ).ok_or(VmExit::ReadFault(addr))?;
        
        // Check for permissions and detect read from uninitialized memory.
        for (i, p) in psl.iter().enumerate() {
            if (p.0 & PERM_READ) == 0 { 
                return Err(VmExit::ReadFault(VirtAddr(addr.0 + i)));
            }

            if (p.0 & PERM_RAW) == 0 {
                return Err(VmExit::ReadUninit(VirtAddr(addr.0 + i)));
            }

        }
        
        Ok(())
    }
    
    /// Check the necessary permissions for performing a write from within
    /// the vm. It returns the faulting reason in a `VmExit`.
    /// It performs the required bound checking and if it doesn't
    /// return an error it is safe to access the `Mem::mem` and `Mem::perms`
    /// buffers in the range [addr, addr+size) without faulting in any way
    /// or overflowing the addition `addr+size` (this condition is checked for).
    pub fn check_perms_write(&self, addr: VirtAddr, size: usize)
        -> Result<(), VmExit> {
         // Get a slice to the required permissions and check for bounds
        let psl = self.perms.get(
            addr.0 ..
            addr.0.checked_add(size).ok_or(VmExit::AddrOverflow(addr))?
            ).ok_or(VmExit::WriteFault(addr))?;
        
        // Check for `PERM_WRITE` permission on all bytes.
        for (i, p) in psl.iter().enumerate() {
            if (p.0 & PERM_WRITE) == 0 { 
                return Err(VmExit::WriteFault(VirtAddr(addr.0 + i)))
            }
        }

        Ok(())
    }
 
    /// Check the necessary permissions for performing a exec from within
    /// the vm. It returns the faulting reason in a `VmExit`.
    /// It performs the required bound checking and if it doesn't
    /// return an error it is safe to access the `Mem::mem` and `Mem::perms`
    /// buffers in the range [addr, addr+size) without faulting in any way
    /// or overflowing the addition `addr+size` (this condition is checked for).
    pub fn check_perms_exec(&self, addr: VirtAddr, size: usize)
        -> Result<(), VmExit> {
        // Get a slice to the required permissions and check for bounds
        let psl = self.perms.get(
            addr.0 ..
            addr.0.checked_add(size).ok_or(VmExit::AddrOverflow(addr))?
            ).ok_or(VmExit::ExecFault(addr))?;
        
        // Check for `PERM_EXEC` permission on all bytes.
        for (i, p) in psl.iter().enumerate() {
            if (p.0 & PERM_EXEC) == 0 { 
                return Err(VmExit::ExecFault(VirtAddr(addr.0 + i)));
            }

            if (p.0 & PERM_RAW) == 0 { 
                return Err(VmExit::ReadUninit(VirtAddr(addr.0 + i)));
            }

        }

        Ok(())
    }

    /// Reads guest memory from `addr` into `buf`. Checks for `PERM_READ`.
    pub fn read(&self, addr: VirtAddr, buf: &mut [u8]) -> Result<(), VmExit> { 
        self.check_perms_read(addr, buf.len())?;
        // This copy_from_slice is safe because of the previous check.
        buf.copy_from_slice(&self.mem[addr.0 .. addr.0 + buf.len()]);
        Ok(())
    }
 
    /// Reads guest memory from `addr` into `buf`. Checks for `PERM_EXEC`,
    /// not `PERM_READ`.
    pub fn read_exec(&self, addr: VirtAddr, buf: &mut  [u8])
        -> Result<(), VmExit> {
        self.check_perms_exec(addr, buf.len())?;
        
        buf.copy_from_slice(&self.mem[addr.0 .. addr.0 + buf.len()]);
        Ok(())
    }


    /// Writes `buf` into the guest VA space at `addr`. Checks for `PERM_WRITE`.
    pub fn write(&mut self, addr: VirtAddr, buf: &[u8]) -> Result<(), VmExit> {
        self.check_perms_write(addr, buf.len())?;
        // After this check the following accesses are safe.

        self.mem[addr.0 .. addr.0 + buf.len()].copy_from_slice(buf);
        
        // Set the RAW bits. See `Perm`.
        self.perms.get_mut(addr.0 .. addr.0 + buf.len()).unwrap()
            .iter_mut().for_each(|x| x.0 |= PERM_RAW);

        // Set the memory as dirty
        self.set_dirty(addr, buf.len());    
        
        Ok(())
    }

    /// Set the permissions `perm` into the bitset of permissions for
    /// the guest memory range `[addr, addr+size)`. Already set bits are
    /// not cleared.
    pub fn add_perms(&mut self, addr: VirtAddr, size: usize, perm: Perm)
        -> Result<(), ()> {
        self.perms.get_mut(addr.0 .. addr.0.checked_add(size).ok_or(())?)
            .ok_or(())?.iter_mut()
            .for_each(|x| x.0 |= perm.0);

        Ok(())
    }
    
    pub fn set_perms(&mut self, addr: VirtAddr, size: usize, perm: Perm)
        -> Result<(), ()> {
        self.perms.get_mut(addr.0 .. addr.0.checked_add(size).ok_or(())?)
            .ok_or(())?.iter_mut()
            .for_each(|x| x.0 = perm.0);

        Ok(())
    }

    pub fn remove_perms(&mut self, addr: VirtAddr, size: usize, perm: Perm)
        -> Result<(), ()> {
        self.perms.get_mut(addr.0 .. addr.0.checked_add(size).ok_or(())?)
            .ok_or(())?.iter_mut()
            .for_each(|x| x.0 &= !(perm.0) );

        Ok(())
    }
    
    // XXX: Refactor these using generics.
    // Read/write native integers instead of buffers of bytes.
    #[inline]
    pub fn read_u32_le(&self, addr: VirtAddr) -> Result<u32, VmExit> {
        self.check_perms_read(addr, 4)?;
        Ok(u32::from_le_bytes( (&self.mem[addr.0 .. addr.0 + 4])
                              .try_into().unwrap() ))
    }
    
    #[inline]
    pub fn read_u32_le_exec(&self, addr: VirtAddr) -> Result<u32, VmExit> {
        self.check_perms_exec(addr, 4)?;
        Ok(u32::from_le_bytes( (&self.mem[addr.0 .. addr.0 + 4])
                              .try_into().unwrap() ))
    }
    
    #[inline]
    pub fn read_u16_le(&self, addr: VirtAddr) -> Result<u16, VmExit> {
        self.check_perms_read(addr, 2)?;
        Ok(u16::from_le_bytes( (&self.mem[addr.0 .. addr.0 + 2])
                              .try_into().unwrap() ))
    }
    
    #[inline]
    pub fn read_u8_le(&self, addr: VirtAddr) -> Result<u8, VmExit> {
        self.check_perms_read(addr, 1)?;
        Ok(u8::from_le_bytes( (&self.mem[addr.0 .. addr.0 + 1])
                              .try_into().unwrap() ))
    }
    
    #[inline]
    pub fn write_u32_le(&mut self, addr: VirtAddr, val: u32)
        -> Result<(), VmExit> {
        let sl = unsafe {
            core::slice::from_raw_parts(&val as *const u32 as *const u8, 4)
        };
        self.write(addr, sl);
        Ok(())
    }
    
    #[inline]
    pub fn write_u16_le(&mut self, addr: VirtAddr, val: u16)
        -> Result<(), VmExit> {
        let sl = unsafe {
            core::slice::from_raw_parts(&val as *const u16 as *const u8,
                                        core::mem::size_of::<u16>())
        };
        self.write(addr, sl);
        Ok(())
    }

    #[inline]
    pub fn write_u8_le(&mut self, addr: VirtAddr, val: u8)
        -> Result<(), VmExit> {
        let sl = unsafe {
            core::slice::from_raw_parts(&val as *const u8,
                                        core::mem::size_of::<u8>())
        };
        self.write(addr, sl);
        Ok(())
    }

}
