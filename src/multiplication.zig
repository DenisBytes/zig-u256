const std = @import("std");

/// Computes (hi * 2^64 + lo) = z + (x * y) + carry.
pub fn umulStep(z: u64, x: u64, y: u64, carry: u64) struct { hi: u64, lo: u64 } {
    // Compute x * y as 128-bit result
    const product = @as(u128, x) * @as(u128, y);
    var hi = @as(u64, @truncate(product >> 64));
    var lo = @as(u64, @truncate(product));

    // Add carry to lo
    const add1 = @addWithOverflow(lo, carry);
    lo = add1[0];
    const carry1 = add1[1];

    // Add carry1 to hi
    const add2 = @addWithOverflow(hi, @as(u64, carry1));
    hi = add2[0];

    // Add z to lo
    const add3 = @addWithOverflow(lo, z);
    lo = add3[0];
    const carry2 = add3[1];

    // Add carry2 to hi
    const add4 = @addWithOverflow(hi, @as(u64, carry2));
    hi = add4[0];

    return .{ .hi = hi, .lo = lo };
}

/// Computes (hi * 2^64 + lo) = z + (x * y).
pub fn umulHop(z: u64, x: u64, y: u64) struct { hi: u64, lo: u64 } {
    // Compute x * y as 128-bit result
    const product = @as(u128, x) * @as(u128, y);
    var hi = @as(u64, @truncate(product >> 64));
    var lo = @as(u64, @truncate(product));

    // Add z to lo
    const add1 = @addWithOverflow(lo, z);
    lo = add1[0];
    const carry = add1[1];

    // Add carry to hi
    const add2 = @addWithOverflow(hi, @as(u64, carry));
    hi = add2[0];

    return .{ .hi = hi, .lo = lo };
}

/// Computes full 256 x 256 -> 512 multiplication.
/// x and y are the input 256-bit numbers (4 limbs each).
/// res is the output 512-bit result (8 limbs).
pub fn umul(x: *const [4]u64, y: *const [4]u64, res: *[8]u64) void {
    var carry: u64 = 0;
    var carry4: u64 = 0;
    var carry5: u64 = 0;
    var carry6: u64 = 0;
    var res1: u64 = 0;
    var res2: u64 = 0;
    var res3: u64 = 0;
    var res4: u64 = 0;
    var res5: u64 = 0;

    // First row: multiply by y[0]
    const p0 = @as(u128, x[0]) * @as(u128, y[0]);
    carry = @as(u64, @truncate(p0 >> 64));
    res[0] = @as(u64, @truncate(p0));

    const r1 = umulHop(carry, x[1], y[0]);
    carry = r1.hi;
    res1 = r1.lo;

    const r2 = umulHop(carry, x[2], y[0]);
    carry = r2.hi;
    res2 = r2.lo;

    const r3 = umulHop(carry, x[3], y[0]);
    carry4 = r3.hi;
    res3 = r3.lo;

    // Second row: multiply by y[1]
    const r4 = umulHop(res1, x[0], y[1]);
    carry = r4.hi;
    res[1] = r4.lo;

    const r5 = umulStep(res2, x[1], y[1], carry);
    carry = r5.hi;
    res2 = r5.lo;

    const r6 = umulStep(res3, x[2], y[1], carry);
    carry = r6.hi;
    res3 = r6.lo;

    const r7 = umulStep(carry4, x[3], y[1], carry);
    carry5 = r7.hi;
    res4 = r7.lo;

    // Third row: multiply by y[2]
    const r8 = umulHop(res2, x[0], y[2]);
    carry = r8.hi;
    res[2] = r8.lo;

    const r9 = umulStep(res3, x[1], y[2], carry);
    carry = r9.hi;
    res3 = r9.lo;

    const r10 = umulStep(res4, x[2], y[2], carry);
    carry = r10.hi;
    res4 = r10.lo;

    const r11 = umulStep(carry5, x[3], y[2], carry);
    carry6 = r11.hi;
    res5 = r11.lo;

    // Fourth row: multiply by y[3]
    const r12 = umulHop(res3, x[0], y[3]);
    carry = r12.hi;
    res[3] = r12.lo;

    const r13 = umulStep(res4, x[1], y[3], carry);
    carry = r13.hi;
    res[4] = r13.lo;

    const r14 = umulStep(res5, x[2], y[3], carry);
    carry = r14.hi;
    res[5] = r14.lo;

    const r15 = umulStep(carry6, x[3], y[3], carry);
    res[7] = r15.hi;
    res[6] = r15.lo;
}

// Tests
const testing = std.testing;

test "umulHop - simple" {
    const result = umulHop(10, 5, 3);
    // (5 * 3) + 10 = 15 + 10 = 25
    try testing.expectEqual(@as(u64, 0), result.hi);
    try testing.expectEqual(@as(u64, 25), result.lo);
}

test "umulHop - with overflow" {
    const result = umulHop(100, 0xFFFFFFFFFFFFFFFF, 2);
    // (0xFFFFFFFFFFFFFFFF * 2) = 0x1FFFFFFFFFFFFFFFE
    // 0x1FFFFFFFFFFFFFFFE + 100 = 0x1FFFFFFFFFFFFFFFE + 0x64 = 0x20000000000000062
    // hi = 2, lo = 98
    try testing.expectEqual(@as(u64, 2), result.hi);
    try testing.expectEqual(@as(u64, 98), result.lo);
}

test "umulStep - simple" {
    const result = umulStep(10, 5, 3, 7);
    // (5 * 3) + 7 + 10 = 15 + 7 + 10 = 32
    try testing.expectEqual(@as(u64, 0), result.hi);
    try testing.expectEqual(@as(u64, 32), result.lo);
}

test "umulStep - with overflow" {
    const result = umulStep(100, 0xFFFFFFFFFFFFFFFF, 2, 50);
    // (0xFFFFFFFFFFFFFFFF * 2) = 0x1FFFFFFFFFFFFFFFE
    // + 50 = 0x1FFFFFFFFFFFFFF30
    // + 100 = 0x1FFFFFFFFFFFFFF94 = 0x20000000000000094
    // hi = 2, lo = 148
    try testing.expectEqual(@as(u64, 2), result.hi);
    try testing.expectEqual(@as(u64, 148), result.lo);
}

test "umul - simple multiplication" {
    var x = [_]u64{ 2, 0, 0, 0 };
    var y = [_]u64{ 3, 0, 0, 0 };
    var res: [8]u64 = undefined;

    umul(&x, &y, &res);

    // 2 * 3 = 6
    try testing.expectEqual(@as(u64, 6), res[0]);
    try testing.expectEqual(@as(u64, 0), res[1]);
    try testing.expectEqual(@as(u64, 0), res[2]);
    try testing.expectEqual(@as(u64, 0), res[3]);
}

test "umul - larger values" {
    var x = [_]u64{ 0xFFFFFFFFFFFFFFFF, 0, 0, 0 };
    var y = [_]u64{ 2, 0, 0, 0 };
    var res: [8]u64 = undefined;

    umul(&x, &y, &res);

    // (2^64 - 1) * 2 = 2^65 - 2
    try testing.expectEqual(@as(u64, 0xFFFFFFFFFFFFFFFE), res[0]);
    try testing.expectEqual(@as(u64, 1), res[1]);
    try testing.expectEqual(@as(u64, 0), res[2]);
}

test "umul - full width multiplication" {
    var x = [_]u64{ 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF };
    var y = [_]u64{ 2, 0, 0, 0 };
    var res: [8]u64 = undefined;

    umul(&x, &y, &res);

    // (2^256 - 1) * 2 = 2^257 - 2
    try testing.expectEqual(@as(u64, 0xFFFFFFFFFFFFFFFE), res[0]);
    try testing.expectEqual(@as(u64, 0xFFFFFFFFFFFFFFFF), res[1]);
    try testing.expectEqual(@as(u64, 0xFFFFFFFFFFFFFFFF), res[2]);
    try testing.expectEqual(@as(u64, 0xFFFFFFFFFFFFFFFF), res[3]);
    try testing.expectEqual(@as(u64, 1), res[4]);
    try testing.expectEqual(@as(u64, 0), res[5]);
}
