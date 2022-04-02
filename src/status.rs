use crate::Slice;
use std::{
    alloc::{alloc, dealloc, Layout},
    fmt::Display,
    ptr,
};

#[derive(PartialEq)]
enum Code {
    Ok,
    NotFound,
    Corruption,
    NotSupported,
    InvalidArgument,
    IOError,
}
impl From<Code> for u8 {
    fn from(c: Code) -> Self {
        match c {
            Code::Ok => 0,
            Code::NotFound => 1,
            Code::Corruption => 2,
            Code::NotSupported => 3,
            Code::InvalidArgument => 4,
            Code::IOError => 5,
        }
    }
}
impl From<u8> for Code {
    fn from(x: u8) -> Self {
        match x {
            0 => Code::Ok,
            1 => Code::NotFound,
            2 => Code::Corruption,
            3 => Code::NotSupported,
            4 => Code::InvalidArgument,
            5 => Code::IOError,
            _ => unreachable!(),
        }
    }
}
impl Display for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let type_str = match self {
            Code::Ok => "OK",
            Code::NotFound => "Not Found: ",
            Code::Corruption => "Corruption: ",
            Code::NotSupported => "Not Supported: ",
            Code::InvalidArgument => "Invalid Argument: ",
            Code::IOError => "IO Error: ",
        };
        write!(f, "{}", type_str)
    }
}

struct Status {
    state: *const u8,
}
impl Status {
    fn ok() -> Self {
        Self::default()
    }
    fn not_found(msg: &Slice) -> Self {
        Self::build(Code::NotFound, msg, &Slice::default())
    }
    fn not_found2(msg: &Slice, msg2: &Slice) -> Self {
        Self::build(Code::NotFound, msg, msg2)
    }
    fn corruption(msg: &Slice) -> Self {
        Self::build(Code::Corruption, msg, &Slice::default())
    }
    fn corruption2(msg: &Slice, msg2: &Slice) -> Self {
        Self::build(Code::Corruption, msg, msg2)
    }
    fn not_supported(msg: &Slice) -> Self {
        Self::build(Code::NotSupported, msg, &Slice::default())
    }
    fn not_supported2(msg: &Slice, msg2: &Slice) -> Self {
        Self::build(Code::NotSupported, msg, msg2)
    }
    fn invalid_argument(msg: &Slice) -> Self {
        Self::build(Code::InvalidArgument, msg, &Slice::default())
    }
    fn invalid_argument2(msg: &Slice, msg2: &Slice) -> Self {
        Self::build(Code::InvalidArgument, msg, msg2)
    }
    fn io_error(msg: &Slice) -> Self {
        Self::build(Code::IOError, msg, &Slice::default())
    }
    fn io_error2(msg: &Slice, msg2: &Slice) -> Self {
        Self::build(Code::IOError, msg, msg2)
    }

    fn is_ok(&self) -> bool {
        self.state.is_null()
    }
    fn is_not_found(&self) -> bool {
        self.code() == Code::NotFound
    }
    fn is_corruption(&self) -> bool {
        self.code() == Code::Corruption
    }
    fn is_not_supported(&self) -> bool {
        self.code() == Code::NotSupported
    }
    fn is_invalid_argument(&self) -> bool {
        self.code() == Code::InvalidArgument
    }
    fn is_io_error(&self) -> bool {
        self.code() == Code::IOError
    }
}
impl Status {
    fn build(code: Code, msg: &Slice, msg2: &Slice) -> Self {
        assert!(code != Code::Ok);
        let len1 = msg.size();
        let len2 = msg2.size();
        let size = if len2 == 0 { len1 } else { len1 + len2 + 2 };
        unsafe {
            let result =
                alloc(Layout::from_size_align(size + 5, std::mem::align_of::<*mut u8>()).unwrap());
            ptr::copy_nonoverlapping(
                &size as *const usize as *const u8,
                result,
                std::mem::size_of_val(&size),
            );
            ptr::write(result.add(4), code.into());
            ptr::copy_nonoverlapping(msg.data(), result.add(5), len1);
            if len2 != 0 {
                ptr::write(result.add(5 + len1), ':' as u8);
                ptr::write(result.add(6 + len1), ' ' as u8);
                ptr::copy_nonoverlapping(msg2.data(), result.add(7 + len1), len2);
            }
            Self { state: result }
        }
    }
    fn code(&self) -> Code {
        if self.state.is_null() {
            Code::Ok
        } else {
            unsafe { (*self.state.add(4)).into() }
        }
    }
    fn copy_state(s: *const u8) -> *const u8 {
        let size: usize = 0;
        unsafe {
            ptr::copy_nonoverlapping(
                s,
                &size as *const usize as *const u8 as *mut u8,
                std::mem::size_of_val(&size),
            );
            let result =
                alloc(Layout::from_size_align(size + 5, std::mem::align_of::<*mut u8>()).unwrap());
            ptr::copy_nonoverlapping(s, result, size + 5);
            result
        }
    }
}
impl Drop for Status {
    fn drop(&mut self) {
        // ptr::drop_in_place(self.state);
        unsafe {
            let size: usize = 0;
            ptr::copy_nonoverlapping(
                self.state,
                &size as *const usize as *const u8 as *mut u8,
                std::mem::size_of_val(&size),
            );
            dealloc(
                self.state as *mut u8,
                Layout::from_size_align(size + 5, std::mem::align_of::<*mut u8>()).unwrap(),
            )
        }
    }
}

impl Default for Status {
    fn default() -> Self {
        Self {
            state: ptr::null_mut(),
        }
    }
}
impl Clone for Status {
    fn clone(&self) -> Self {
        if self.state.is_null() {
            Self::default()
        } else {
            Self {
                state: Self::copy_state(self.state),
            }
        }
    }
}
impl Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.state.is_null() {
            write!(f, "OK")
        } else {
            let desc: String = unsafe {
                let size: usize = 0;
                ptr::copy_nonoverlapping(
                    self.state,
                    &size as *const usize as *const u8 as *mut u8,
                    std::mem::size_of_val(&size),
                );
                Slice::new(self.state.add(5), size).into()
            };
            write!(f, "{}{}", self.code(), desc)
        }
    }
}
