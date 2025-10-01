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
    /// sets z to that value, and returns self.
    /// If buf is larger than 32 bytes, only the last 32 bytes are used.
    pub fn setBytes(self: *U256, buf: []const u8) *U256 {
        const len = buf.len;

        if (len == 0) {
            return self.clear();
        }

        // If larger than 32 bytes, use only the last 32 bytes
        const effective_buf = if (len > 32) buf[len - 32 ..] else buf;
        const effective_len = @min(len, 32);

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
