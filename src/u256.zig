const std = @import("std");
const builtin = @import("builtin");
const mem = std.mem;
const math = std.math;
const assert = std.debug.assert;

/// U256 represents a 256-bit unsigned integer as an array of 4 u64 limbs.
/// Limbs are stored in little-endian order:
/// - limbs[0] is the least significant
/// - limbs[3] is the most significant
pub const U256 = struct {
    limbs: [4]u64,

    /// Creates a new U256 initialized to zero.
    pub fn initZero() U256 {
        return .{ .limbs = [_]u64{0} ** 4 };
    }

    /// Creates a new U256 from a u64 value.
    pub fn init(val: u64) U256 {
        return .{ .limbs = [_]u64{ val, 0, 0, 0 } };
    }

    /// Sets self to the value of a u64 and returns self.
    pub fn setInt(self: *U256, val: u64) *U256 {
        self.limbs[0] = val;
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
        return self;
    }

    /// Clears self (sets to zero) and returns self.
    pub fn clear(self: *U256) *U256 {
        self.limbs = [_]u64{0} ** 4;
        return self;
    }

    /// Interprets buf as the bytes of a big-endian unsigned integer,
    /// sets self to that value, and returns self.
    /// If buf is larger than 32 bytes, only the last 32 bytes are used.
    pub fn setBytes(self: *U256, buf: []const u8) *U256 {
        if (buf.len == 0) {
            return self.clear();
        }

        // If larger than 32 bytes, use only the last 32 bytes
        const effective_buf = if (buf.len > 32) buf[buf.len - 32 ..] else buf;
        const effective_len = @min(buf.len, 32);

        switch (effective_len) {
            1 => self.setBytes1(effective_buf),
            2 => self.setBytes2(effective_buf),
            3 => self.setBytes3(effective_buf),
            4 => self.setBytes4(effective_buf),
            5 => self.setBytes5(effective_buf),
            6 => self.setBytes6(effective_buf),
            7 => self.setBytes7(effective_buf),
            8 => self.setBytes8(effective_buf),
            9 => self.setBytes9(effective_buf),
            10 => self.setBytes10(effective_buf),
            11 => self.setBytes11(effective_buf),
            12 => self.setBytes12(effective_buf),
            13 => self.setBytes13(effective_buf),
            14 => self.setBytes14(effective_buf),
            15 => self.setBytes15(effective_buf),
            16 => self.setBytes16(effective_buf),
            17 => self.setBytes17(effective_buf),
            18 => self.setBytes18(effective_buf),
            19 => self.setBytes19(effective_buf),
            20 => self.setBytes20(effective_buf),
            21 => self.setBytes21(effective_buf),
            22 => self.setBytes22(effective_buf),
            23 => self.setBytes23(effective_buf),
            24 => self.setBytes24(effective_buf),
            25 => self.setBytes25(effective_buf),
            26 => self.setBytes26(effective_buf),
            27 => self.setBytes27(effective_buf),
            28 => self.setBytes28(effective_buf),
            29 => self.setBytes29(effective_buf),
            30 => self.setBytes30(effective_buf),
            31 => self.setBytes31(effective_buf),
            32 => self.setBytes32(effective_buf),
            else => unreachable,
        }

        return self;
    }

    /// bytes32 returns the value of self as a 32-byte big-endian array.
    pub fn bytes32(self: U256) [32]u8 {
        var b: [32]u8 = undefined;

        mem.writeInt(u64, b[0..8], self.limbs[3], .big);
        mem.writeInt(u64, b[8..16], self.limbs[2], .big);
        mem.writeInt(u64, b[16..24], self.limbs[1], .big);
        mem.writeInt(u64, b[24..32], self.limbs[0], .big);

        return b;
    }

    /// Returns the number of bits required to represent self.
    pub fn bitLen(self: U256) usize {
        if (self.limbs[3] != 0) {
            return @as(usize, 192) + @as(usize, 64 - @clz(self.limbs[3]));
        }
        if (self.limbs[2] != 0) {
            return @as(usize, 128) + @as(usize, 64 - @clz(self.limbs[2]));
        }
        if (self.limbs[1] != 0) {
            return @as(usize, 64) + @as(usize, 64 - @clz(self.limbs[1]));
        }
        if (self.limbs[0] == 0) {
            return 0;
        }
        return @as(usize, 64 - @clz(self.limbs[0]));
    }

    /// Returns the number of bytes required to represent self.
    pub fn byteLen(self: U256) usize {
        return (self.bitLen() + 7) / 8;
    }

    /// Writes the minimal big-endian representation to the start of buf.
    /// Returns the number of bytes written.
    /// Returns 0 if buf is smaller than the minimal byte length.
    pub fn writeBytes(self: U256, buf: []u8) usize {
        const len = self.byteLen();
        if (buf.len < len) return 0;

        const full = self.bytes32();
        @memcpy(buf[0..len], full[32 - len ..]);
        return len;
    }

    /// Writes bytes to the end of buf (right-padded with the value at the end).
    /// If buf is larger than 32 bytes, fills the first 32 bytes.
    /// If buf is smaller than 32 bytes, only writes the least significant bytes.
    /// Useful for filling fixed-size buffers like Ethereum addresses (20 bytes).
    pub fn writeBytesToEnd(self: U256, buf: []u8) void {
        if (buf.len == 0) return;

        const full = self.bytes32();
        const end: usize = @min(buf.len - 1, 31);

        var i: usize = 0;
        while (i <= end) : (i += 1) {
            buf[end - i] = full[31 - i];
        }
    }

    // setBytes functions for each length (1-32 bytes)

    fn setBytes1(self: *U256, buf: []const u8) void {
        assert(buf.len == 1);
        self.limbs[0] = buf[0];
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes2(self: *U256, buf: []const u8) void {
        assert(buf.len == 2);
        self.limbs[0] = mem.readInt(u16, buf[0..2], .big);
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes3(self: *U256, buf: []const u8) void {
        assert(buf.len == 3);
        self.limbs[0] = (@as(u64, buf[0]) << 16) | mem.readInt(u16, buf[1..3], .big);
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes4(self: *U256, buf: []const u8) void {
        assert(buf.len == 4);
        self.limbs[0] = mem.readInt(u32, buf[0..4], .big);
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes5(self: *U256, buf: []const u8) void {
        assert(buf.len == 5);
        self.limbs[0] = (@as(u64, buf[0]) << 32) | mem.readInt(u32, buf[1..5], .big);
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes6(self: *U256, buf: []const u8) void {
        assert(buf.len == 6);
        self.limbs[0] = (@as(u64, mem.readInt(u16, buf[0..2], .big)) << 32) |
            mem.readInt(u32, buf[2..6], .big);
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes7(self: *U256, buf: []const u8) void {
        assert(buf.len == 7);
        self.limbs[0] = (@as(u64, buf[0]) << 48) |
            (@as(u64, mem.readInt(u16, buf[1..3], .big)) << 32) |
            mem.readInt(u32, buf[3..7], .big);
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes8(self: *U256, buf: []const u8) void {
        assert(buf.len == 8);
        self.limbs[0] = mem.readInt(u64, buf[0..8], .big);
        self.limbs[1] = 0;
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes9(self: *U256, buf: []const u8) void {
        assert(buf.len == 9);
        self.limbs[0] = mem.readInt(u64, buf[1..9], .big);
        self.limbs[1] = buf[0];
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes10(self: *U256, buf: []const u8) void {
        assert(buf.len == 10);
        self.limbs[0] = mem.readInt(u64, buf[2..10], .big);
        self.limbs[1] = mem.readInt(u16, buf[0..2], .big);
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes11(self: *U256, buf: []const u8) void {
        assert(buf.len == 11);
        self.limbs[0] = mem.readInt(u64, buf[3..11], .big);
        self.limbs[1] = (@as(u64, buf[0]) << 16) | mem.readInt(u16, buf[1..3], .big);
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes12(self: *U256, buf: []const u8) void {
        assert(buf.len == 12);
        self.limbs[0] = mem.readInt(u64, buf[4..12], .big);
        self.limbs[1] = mem.readInt(u32, buf[0..4], .big);
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes13(self: *U256, buf: []const u8) void {
        assert(buf.len == 13);
        self.limbs[0] = mem.readInt(u64, buf[5..13], .big);
        self.limbs[1] = (@as(u64, buf[0]) << 32) | mem.readInt(u32, buf[1..5], .big);
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes14(self: *U256, buf: []const u8) void {
        assert(buf.len == 14);
        self.limbs[0] = mem.readInt(u64, buf[6..14], .big);
        self.limbs[1] = (@as(u64, mem.readInt(u16, buf[0..2], .big)) << 32) |
            mem.readInt(u32, buf[2..6], .big);
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes15(self: *U256, buf: []const u8) void {
        assert(buf.len == 15);
        self.limbs[0] = mem.readInt(u64, buf[7..15], .big);
        self.limbs[1] = (@as(u64, buf[0]) << 48) |
            (@as(u64, mem.readInt(u16, buf[1..3], .big)) << 32) |
            mem.readInt(u32, buf[3..7], .big);
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes16(self: *U256, buf: []const u8) void {
        assert(buf.len == 16);
        self.limbs[0] = mem.readInt(u64, buf[8..16], .big);
        self.limbs[1] = mem.readInt(u64, buf[0..8], .big);
        self.limbs[2] = 0;
        self.limbs[3] = 0;
    }

    fn setBytes17(self: *U256, buf: []const u8) void {
        assert(buf.len == 17);
        self.limbs[0] = mem.readInt(u64, buf[9..17], .big);
        self.limbs[1] = mem.readInt(u64, buf[1..9], .big);
        self.limbs[2] = buf[0];
        self.limbs[3] = 0;
    }

    fn setBytes18(self: *U256, buf: []const u8) void {
        assert(buf.len == 18);
        self.limbs[0] = mem.readInt(u64, buf[10..18], .big);
        self.limbs[1] = mem.readInt(u64, buf[2..10], .big);
        self.limbs[2] = mem.readInt(u16, buf[0..2], .big);
        self.limbs[3] = 0;
    }

    fn setBytes19(self: *U256, buf: []const u8) void {
        assert(buf.len == 19);
        self.limbs[0] = mem.readInt(u64, buf[11..19], .big);
        self.limbs[1] = mem.readInt(u64, buf[3..11], .big);
        self.limbs[2] = (@as(u64, buf[0]) << 16) | mem.readInt(u16, buf[1..3], .big);
        self.limbs[3] = 0;
    }

    fn setBytes20(self: *U256, buf: []const u8) void {
        assert(buf.len == 20);
        self.limbs[0] = mem.readInt(u64, buf[12..20], .big);
        self.limbs[1] = mem.readInt(u64, buf[4..12], .big);
        self.limbs[2] = mem.readInt(u32, buf[0..4], .big);
        self.limbs[3] = 0;
    }

    fn setBytes21(self: *U256, buf: []const u8) void {
        assert(buf.len == 21);
        self.limbs[0] = mem.readInt(u64, buf[13..21], .big);
        self.limbs[1] = mem.readInt(u64, buf[5..13], .big);
        self.limbs[2] = (@as(u64, buf[0]) << 32) | mem.readInt(u32, buf[1..5], .big);
        self.limbs[3] = 0;
    }

    fn setBytes22(self: *U256, buf: []const u8) void {
        assert(buf.len == 22);
        self.limbs[0] = mem.readInt(u64, buf[14..22], .big);
        self.limbs[1] = mem.readInt(u64, buf[6..14], .big);
        self.limbs[2] = (@as(u64, mem.readInt(u16, buf[0..2], .big)) << 32) |
            mem.readInt(u32, buf[2..6], .big);
        self.limbs[3] = 0;
    }

    fn setBytes23(self: *U256, buf: []const u8) void {
        assert(buf.len == 23);
        self.limbs[0] = mem.readInt(u64, buf[15..23], .big);
        self.limbs[1] = mem.readInt(u64, buf[7..15], .big);
        self.limbs[2] = (@as(u64, buf[0]) << 48) |
            (@as(u64, mem.readInt(u16, buf[1..3], .big)) << 32) |
            mem.readInt(u32, buf[3..7], .big);
        self.limbs[3] = 0;
    }

    fn setBytes24(self: *U256, buf: []const u8) void {
        assert(buf.len == 24);
        self.limbs[0] = mem.readInt(u64, buf[16..24], .big);
        self.limbs[1] = mem.readInt(u64, buf[8..16], .big);
        self.limbs[2] = mem.readInt(u64, buf[0..8], .big);
        self.limbs[3] = 0;
    }

    fn setBytes25(self: *U256, buf: []const u8) void {
        assert(buf.len == 25);
        self.limbs[0] = mem.readInt(u64, buf[17..25], .big);
        self.limbs[1] = mem.readInt(u64, buf[9..17], .big);
        self.limbs[2] = mem.readInt(u64, buf[1..9], .big);
        self.limbs[3] = buf[0];
    }

    fn setBytes26(self: *U256, buf: []const u8) void {
        assert(buf.len == 26);
        self.limbs[0] = mem.readInt(u64, buf[18..26], .big);
        self.limbs[1] = mem.readInt(u64, buf[10..18], .big);
        self.limbs[2] = mem.readInt(u64, buf[2..10], .big);
        self.limbs[3] = mem.readInt(u16, buf[0..2], .big);
    }

    fn setBytes27(self: *U256, buf: []const u8) void {
        assert(buf.len == 27);
        self.limbs[0] = mem.readInt(u64, buf[19..27], .big);
        self.limbs[1] = mem.readInt(u64, buf[11..19], .big);
        self.limbs[2] = mem.readInt(u64, buf[3..11], .big);
        self.limbs[3] = (@as(u64, buf[0]) << 16) | mem.readInt(u16, buf[1..3], .big);
    }

    fn setBytes28(self: *U256, buf: []const u8) void {
        assert(buf.len == 28);
        self.limbs[0] = mem.readInt(u64, buf[20..28], .big);
        self.limbs[1] = mem.readInt(u64, buf[12..20], .big);
        self.limbs[2] = mem.readInt(u64, buf[4..12], .big);
        self.limbs[3] = mem.readInt(u32, buf[0..4], .big);
    }

    fn setBytes29(self: *U256, buf: []const u8) void {
        assert(buf.len == 29);
        self.limbs[0] = mem.readInt(u64, buf[21..29], .big);
        self.limbs[1] = mem.readInt(u64, buf[13..21], .big);
        self.limbs[2] = mem.readInt(u64, buf[5..13], .big);
        self.limbs[3] = (@as(u64, buf[0]) << 32) | mem.readInt(u32, buf[1..5], .big);
    }

    fn setBytes30(self: *U256, buf: []const u8) void {
        assert(buf.len == 30);
        self.limbs[0] = mem.readInt(u64, buf[22..30], .big);
        self.limbs[1] = mem.readInt(u64, buf[14..22], .big);
        self.limbs[2] = mem.readInt(u64, buf[6..14], .big);
        self.limbs[3] = (@as(u64, mem.readInt(u16, buf[0..2], .big)) << 32) |
            mem.readInt(u32, buf[2..6], .big);
    }

    fn setBytes31(self: *U256, buf: []const u8) void {
        assert(buf.len == 31);
        self.limbs[0] = mem.readInt(u64, buf[23..31], .big);
        self.limbs[1] = mem.readInt(u64, buf[15..23], .big);
        self.limbs[2] = mem.readInt(u64, buf[7..15], .big);
        self.limbs[3] = (@as(u64, buf[0]) << 48) |
            (@as(u64, mem.readInt(u16, buf[1..3], .big)) << 32) |
            mem.readInt(u32, buf[3..7], .big);
    }

    fn setBytes32(self: *U256, buf: []const u8) void {
        assert(buf.len == 32);
        self.limbs[0] = mem.readInt(u64, buf[24..32], .big);
        self.limbs[1] = mem.readInt(u64, buf[16..24], .big);
        self.limbs[2] = mem.readInt(u64, buf[8..16], .big);
        self.limbs[3] = mem.readInt(u64, buf[0..8], .big);
    }
};

test "U256 initZero" {
    const z = U256.initZero();
    try std.testing.expectEqual(@as(u64, 0), z.limbs[0]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[1]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[2]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[3]);
}

test "U256 init" {
    const z = U256.init(42);
    try std.testing.expectEqual(@as(u64, 42), z.limbs[0]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[1]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[2]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[3]);
}

test "U256 setBytes - empty" {
    var z = U256.initZero();
    _ = z.setBytes(&[_]u8{});
    try std.testing.expectEqual(@as(u64, 0), z.limbs[0]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[1]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[2]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[3]);
}

test "U256 setBytes - single byte" {
    var z = U256.initZero();
    _ = z.setBytes(&[_]u8{0xFF});
    try std.testing.expectEqual(@as(u64, 0xFF), z.limbs[0]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[1]);
}

test "U256 setBytes - 8 bytes" {
    var z = U256.initZero();
    _ = z.setBytes(&[_]u8{ 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08 });
    try std.testing.expectEqual(@as(u64, 0x0102030405060708), z.limbs[0]);
    try std.testing.expectEqual(@as(u64, 0), z.limbs[1]);
}

test "U256 setBytes - 32 bytes" {
    var z = U256.initZero();
    const bytes = [_]u8{
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,
        0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,
    };
    _ = z.setBytes(&bytes);
    try std.testing.expectEqual(@as(u64, 0x191A1B1C1D1E1F20), z.limbs[0]);
    try std.testing.expectEqual(@as(u64, 0x1112131415161718), z.limbs[1]);
    try std.testing.expectEqual(@as(u64, 0x090A0B0C0D0E0F10), z.limbs[2]);
    try std.testing.expectEqual(@as(u64, 0x0102030405060708), z.limbs[3]);
}

test "U256 setBytes - larger than 32 bytes" {
    var z = U256.initZero();
    const bytes = [_]u8{
        0xFF, 0xFF, 0xFF, 0xFF,
        0x01, 0x02, 0x03, 0x04,
        0x05, 0x06, 0x07, 0x08,
        0x09, 0x0A, 0x0B, 0x0C,
        0x0D, 0x0E, 0x0F, 0x10,
        0x11, 0x12, 0x13, 0x14,
        0x15, 0x16, 0x17, 0x18,
        0x19, 0x1A, 0x1B, 0x1C,
        0x1D, 0x1E, 0x1F, 0x20,
    };
    _ = z.setBytes(&bytes);
    try std.testing.expectEqual(@as(u64, 0x191A1B1C1D1E1F20), z.limbs[0]);
    try std.testing.expectEqual(@as(u64, 0x1112131415161718), z.limbs[1]);
    try std.testing.expectEqual(@as(u64, 0x090A0B0C0D0E0F10), z.limbs[2]);
    try std.testing.expectEqual(@as(u64, 0x0102030405060708), z.limbs[3]);
}

test "U256 bitLen - zero" {
    const z = U256.initZero();
    try std.testing.expectEqual(@as(usize, 0), z.bitLen());
}

test "U256 bitLen - single bit" {
    const z = U256.init(1);
    try std.testing.expectEqual(@as(usize, 1), z.bitLen());
}

test "U256 bitLen - 8 bits" {
    const z = U256.init(0xFF);
    try std.testing.expectEqual(@as(usize, 8), z.bitLen());
}

test "U256 bitLen - 64 bits" {
    const z = U256.init(0xFFFFFFFFFFFFFFFF);
    try std.testing.expectEqual(@as(usize, 64), z.bitLen());
}

test "U256 bitLen - spanning limbs" {
    var z = U256.initZero();
    z.limbs[1] = 0xFF;
    try std.testing.expectEqual(@as(usize, 64 + 8), z.bitLen());
}

test "U256 bitLen - max value" {
    var z = U256.initZero();
    z.limbs[3] = 0xFFFFFFFFFFFFFFFF;
    z.limbs[2] = 0xFFFFFFFFFFFFFFFF;
    z.limbs[1] = 0xFFFFFFFFFFFFFFFF;
    z.limbs[0] = 0xFFFFFFFFFFFFFFFF;
    try std.testing.expectEqual(@as(usize, 256), z.bitLen());
}

test "U256 byteLen - zero" {
    const z = U256.initZero();
    try std.testing.expectEqual(@as(usize, 0), z.byteLen());
}

test "U256 byteLen - single byte" {
    const z = U256.init(0xFF);
    try std.testing.expectEqual(@as(usize, 1), z.byteLen());
}

test "U256 byteLen - two bytes" {
    const z = U256.init(0x0100);
    try std.testing.expectEqual(@as(usize, 2), z.byteLen());
}

test "U256 byteLen - 32 bytes" {
    var z = U256.initZero();
    z.limbs[3] = 0x0100000000000000;
    try std.testing.expectEqual(@as(usize, 32), z.byteLen());
}

test "U256 bytes32 - round trip" {
    const original = [_]u8{
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,
        0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,
    };
    var z = U256.initZero();
    _ = z.setBytes(&original);
    const result = z.bytes32();
    try std.testing.expectEqualSlices(u8, &original, &result);
}

test "U256 bytes32 - small value" {
    const z = U256.init(0x42);
    const result = z.bytes32();
    try std.testing.expectEqual(@as(u8, 0), result[0]);
    try std.testing.expectEqual(@as(u8, 0x42), result[31]);
}

test "U256 writeBytes - sufficient buffer" {
    const z = U256.init(0x1234);
    var buf: [32]u8 = undefined;
    const written = z.writeBytes(&buf);
    try std.testing.expectEqual(@as(usize, 2), written);
    try std.testing.expectEqual(@as(u8, 0x12), buf[0]);
    try std.testing.expectEqual(@as(u8, 0x34), buf[1]);
}

test "U256 writeBytes - insufficient buffer" {
    const z = U256.init(0x123456);
    var buf: [2]u8 = undefined;
    const written = z.writeBytes(&buf);
    try std.testing.expectEqual(@as(usize, 0), written);
}

test "U256 writeBytes - zero value" {
    const z = U256.initZero();
    var buf: [1]u8 = undefined;
    const written = z.writeBytes(&buf);
    try std.testing.expectEqual(@as(usize, 0), written);
}

test "U256 writeBytes - full 32 bytes" {
    var z = U256.initZero();
    _ = z.setBytes(&[_]u8{
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,
        0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,
    });
    var buf: [32]u8 = undefined;
    const written = z.writeBytes(&buf);
    try std.testing.expectEqual(@as(usize, 32), written);
    try std.testing.expectEqual(@as(u8, 0x01), buf[0]);
    try std.testing.expectEqual(@as(u8, 0x20), buf[31]);
}

test "U256 writeBytesToEnd - 20 byte buffer (Ethereum address)" {
    const z = U256.init(0x1234);
    var buf: [20]u8 = undefined;
    z.writeBytesToEnd(&buf);
    // Should fill from the end with least significant bytes
    try std.testing.expectEqual(@as(u8, 0), buf[0]);
    try std.testing.expectEqual(@as(u8, 0), buf[17]);
    try std.testing.expectEqual(@as(u8, 0x12), buf[18]);
    try std.testing.expectEqual(@as(u8, 0x34), buf[19]);
}

test "U256 writeBytesToEnd - 32 byte buffer" {
    var z = U256.initZero();
    _ = z.setBytes(&[_]u8{
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,
        0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,
    });
    var buf: [32]u8 = undefined;
    z.writeBytesToEnd(&buf);
    try std.testing.expectEqual(@as(u8, 0x01), buf[0]);
    try std.testing.expectEqual(@as(u8, 0x20), buf[31]);
}

test "U256 writeBytesToEnd - 40 byte buffer (larger than 32)" {
    const z = U256.init(0xABCDEF);
    var buf: [40]u8 = [_]u8{0xFF} ** 40;
    z.writeBytesToEnd(&buf);
    // Should fill only first 32 bytes
    try std.testing.expectEqual(@as(u8, 0), buf[0]);
    try std.testing.expectEqual(@as(u8, 0xAB), buf[29]);
    try std.testing.expectEqual(@as(u8, 0xCD), buf[30]);
    try std.testing.expectEqual(@as(u8, 0xEF), buf[31]);
    // Last 8 bytes should remain untouched
    try std.testing.expectEqual(@as(u8, 0xFF), buf[32]);
    try std.testing.expectEqual(@as(u8, 0xFF), buf[39]);
}

test "U256 writeBytesToEnd - empty buffer" {
    const z = U256.init(0x1234);
    var buf: [0]u8 = undefined;
    z.writeBytesToEnd(&buf); // Should not crash
}
