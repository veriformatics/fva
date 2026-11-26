/-!
# WASI preview1 numbering (reviewed spec)

The numbers the 20 declared calls exchange with a guest (`WebAssembly/WASI@fae981ba`
`preview1/witx/typenames.witx`): error codes, rights bits, file types, flags, `whence` and clock
ids. Struct layouts (wasi-libc `wasip1.h`'s static asserts) sit with the calls that write them
(`FVA.Spec.Wasi.Call`).
-/

namespace FVA.Wasi

/-! Error codes (`errno`, u16): the ones the model returns; any of 1–76 is a W outcome. -/
namespace Errno
/-- `badf`: Bad file descriptor. -/
def badf : Nat := 8
/-- `exist`: File exists. -/
def exist : Nat := 20
/-- `fbig`: File too large. -/
def fbig : Nat := 22
/-- `intr`: Interrupted function. -/
def intr : Nat := 27
/-- `inval`: Invalid argument. -/
def inval : Nat := 28
/-- `isdir`: Is a directory. -/
def isdir : Nat := 31
/-- `mfile`: File descriptor value too large. -/
def mfile : Nat := 33
/-- `nametoolong`: Filename too long. -/
def nametoolong : Nat := 37
/-- `noent`: No such file or directory. -/
def noent : Nat := 44
/-- `nospc`: No space left on device. -/
def nospc : Nat := 51
/-- `notdir`: Not a directory or a symbolic link to a directory. -/
def notdir : Nat := 54
/-- `notempty`: Directory not empty. -/
def notempty : Nat := 55
/-- `notsup`: Not supported, or operation not supported on socket. -/
def notsup : Nat := 58
/-- `overflow`: Value too large to be stored in data type. -/
def overflow : Nat := 61
/-- `perm`: Operation not permitted. -/
def perm : Nat := 63
/-- `spipe`: Invalid seek. -/
def spipe : Nat := 70
/-- `notcapable`: Extension: Capabilities insufficient. -/
def notcapable : Nat := 76
end Errno

/-! Rights (`rights`, u64 flags): the bit index of each right the model checks or grants. -/
namespace Right
/-- `fd_datasync`. -/
def fdDatasync : Nat := 0
/-- `fd_read`. -/
def fdRead : Nat := 1
/-- `fd_seek`. -/
def fdSeek : Nat := 2
/-- `fd_fdstat_set_flags`. -/
def fdFdstatSetFlags : Nat := 3
/-- `fd_sync`. -/
def fdSync : Nat := 4
/-- `fd_tell`. -/
def fdTell : Nat := 5
/-- `fd_write`. -/
def fdWrite : Nat := 6
/-- `fd_advise`. -/
def fdAdvise : Nat := 7
/-- `fd_allocate`. -/
def fdAllocate : Nat := 8
/-- `path_create_directory`. -/
def pathCreateDirectory : Nat := 9
/-- `path_create_file`. -/
def pathCreateFile : Nat := 10
/-- `path_link_source`. -/
def pathLinkSource : Nat := 11
/-- `path_link_target`. -/
def pathLinkTarget : Nat := 12
/-- `path_open`. -/
def pathOpen : Nat := 13
/-- `fd_readdir`. -/
def fdReaddir : Nat := 14
/-- `path_readlink`. -/
def pathReadlink : Nat := 15
/-- `path_rename_source`. -/
def pathRenameSource : Nat := 16
/-- `path_rename_target`. -/
def pathRenameTarget : Nat := 17
/-- `path_filestat_get`. -/
def pathFilestatGet : Nat := 18
/-- `path_filestat_set_size`. -/
def pathFilestatSetSize : Nat := 19
/-- `path_filestat_set_times`. -/
def pathFilestatSetTimes : Nat := 20
/-- `fd_filestat_get`. -/
def fdFilestatGet : Nat := 21
/-- `fd_filestat_set_size`. -/
def fdFilestatSetSize : Nat := 22
/-- `fd_filestat_set_times`. -/
def fdFilestatSetTimes : Nat := 23
/-- `path_symlink`. -/
def pathSymlink : Nat := 24
/-- `path_remove_directory`. -/
def pathRemoveDirectory : Nat := 25
/-- `path_unlink_file`. -/
def pathUnlinkFile : Nat := 26
/-- `poll_fd_readwrite`. -/
def pollFdReadwrite : Nat := 27
/-- Bits 0–29 are rights (`sock_shutdown` 28, `sock_accept` 29); higher bits are invalid. -/
def count : Nat := 30
end Right

/-- The mask with the given right bits set. -/
def rights (bits : List Nat) : Nat := (bits.map (2 ^ ·)).sum

/-- `r` holds right `bit`. -/
def has (r bit : Nat) : Bool := r.testBit bit

/-- Flag mask `f` is set in `x`. -/
def flag (x f : Nat) : Bool := x &&& f != 0

/-- Every bit of `a` is set in `b`. -/
def subset (a b : Nat) : Bool := a &&& b == a

/-! File types (`filetype`, u8). -/
namespace Filetype
/-- `unknown`. -/
def unknown : Nat := 0
/-- `directory`. -/
def directory : Nat := 3
/-- `regular_file`. -/
def regularFile : Nat := 4
end Filetype

/-! `fdflags` (u16) bits. -/
namespace Fdflags
/-- `append`. -/
def append : Nat := 1
/-- `dsync`. -/
def dsync : Nat := 2
/-- `nonblock`. -/
def nonblock : Nat := 4
/-- `rsync`. -/
def rsync : Nat := 8
/-- `sync`. -/
def sync : Nat := 16
end Fdflags

/-! `oflags` (u16) bits. -/
namespace Oflags
/-- `creat`. -/
def creat : Nat := 1
/-- `directory`. -/
def directory : Nat := 2
/-- `excl`. -/
def excl : Nat := 4
/-- `trunc`. -/
def trunc : Nat := 8
end Oflags

/-- Clock ids (`clockid`, u32): realtime 0, monotonic 1, process CPU time 2, thread CPU time 3. -/
def clockCount : Nat := 4

end FVA.Wasi
