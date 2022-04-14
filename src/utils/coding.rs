pub fn encode_fixed_32(dst: *mut u8, val: u32) {
    unsafe {
        *dst.offset(0) = (val & 0xFF) as u8;
        *dst.offset(1) = ((val >> 8) & 0xFF) as u8;
        *dst.offset(2) = ((val >> 16) & 0xFF) as u8;
        *dst.offset(3) = ((val >> 24) & 0xFF) as u8;
    }
}

pub fn decode_fixed_32(src: *const u8) -> u32 {
    unsafe {
        (*src.offset(0) as u32)
            | ((*src.offset(1) as u32) << 8)
            | ((*src.offset(2) as u32) << 16)
            | ((*src.offset(3) as u32) << 24)
    }
}

pub fn put_fixed_32(dst: &mut String, val: u32) {
    let mut buf: [u8; 4] = [0; 4];
    encode_fixed_32(&mut buf as *mut u8, val);
    unsafe { dst.push_str(std::str::from_utf8_unchecked(&buf)) };
}
