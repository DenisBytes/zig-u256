const std = @import("std");
const U256 = @import("u256.zig").U256;

/// Computes the reciprocal of d as <^d, ^0> / d.
/// Equivalent to Go's bits.Div64(^d, ^uint64(0), d)
pub fn reciprocal2by1(d: u64) u64 {
    // Compute (2^128 - 2^64) / d = ((~d) << 64 | ~0) / d
    // Since we're dividing a 128-bit number by a 64-bit number,
    // and d is normalized (top bit set), the quotient fits in 64 bits
    const hi = ~d;
    const lo = ~@as(u64, 0);

    // Build the 128-bit dividend
    const dividend: u128 = (@as(u128, hi) << 64) | lo;
    const quotient = dividend / d;

    // The quotient must fit in 64 bits (guaranteed when d is normalized)
    return @truncate(quotient);
}

/// Divides <uh, ul> / d and produces both quotient and remainder.
/// Uses the provided reciprocal of d.
/// Based on "Improved division by invariant integers", Algorithm 4.
pub fn udivrem2by1(uh: u64, ul: u64, d: u64, reciprocal: u64) struct { quot: u64, rem: u64 } {
    // qh:ql = reciprocal * uh
    const mul_result = @mulWithOverflow(reciprocal, uh);
    var ql = mul_result[0];
    var qh: u64 = mul_result[1];

    // ql += ul, with carry
    const add1 = @addWithOverflow(ql, ul);
    ql = add1[0];
    const carry1: u64 = add1[1];

    // qh += uh + carry (three-way add, keep only low 64 bits)
    const add2 = @addWithOverflow(qh, uh);
    const qh_tmp = add2[0];

    const add3 = @addWithOverflow(qh_tmp, carry1);
    qh = add3[0];

    qh +%= 1;

    var r = ul -% (qh *% d);

    if (r > ql) {
        qh -%= 1;
        r +%= d;
    }

    if (r >= d) {
        qh +%= 1;
        r -%= d;
    }

    return .{ .quot = qh, .rem = r };
}

/// Divides u by single normalized word d and produces both quotient and remainder.
/// The quotient is stored in provided quot slice.
/// Returns the remainder.
pub fn udivremBy1(quot: []u64, u: []const u64, d: u64) u64 {
    const reciprocal = reciprocal2by1(d);
    var rem = u[u.len - 1];

    var j: usize = u.len - 1;
    while (j > 0) {
        j -= 1;
        const result = udivrem2by1(rem, u[j], d, reciprocal);
        quot[j] = result.quot;
        rem = result.rem;
    }

    return rem;
}

/// Computes x += y. Returns the carry.
/// Requires x.len >= y.len > 0.
pub fn addTo(x: []u64, y: []const u64) u64 {
    var carry: u1 = 0;

    for (y, 0..) |y_val, i| {
        const add1 = @addWithOverflow(x[i], y_val);
        const add2 = @addWithOverflow(add1[0], carry);
        x[i] = add2[0];
        carry = add1[1] | add2[1];
    }

    return carry;
}

/// Computes x -= y * multiplier. Returns the borrow.
/// Requires x.len >= y.len > 0.
pub fn subMulTo(x: []u64, y: []const u64, multiplier: u64) u64 {
    var borrow: u64 = 0;

    for (y, 0..) |y_val, i| {
        // s = x[i] - borrow
        const sub1 = @subWithOverflow(x[i], borrow);
        const s = sub1[0];
        const carry1: u64 = sub1[1];

        // ph:pl = y[i] * multiplier
        const mul = @mulWithOverflow(y_val, multiplier);
        const pl = mul[0];
        const ph = mul[1];

        // t = s - pl
        const sub2 = @subWithOverflow(s, pl);
        const t = sub2[0];
        const carry2: u64 = sub2[1];

        x[i] = t;
        borrow = ph + carry1 + carry2;
    }

    return borrow;
}

/// Implements the division of u by normalized multiple word d using Knuth's division algorithm.
/// The quotient is stored in provided quot - len(u)-len(d) words.
/// Updates u to contain the remainder - len(d) words.
pub fn udivremKnuth(quot: []u64, u: []u64, d: []const u64) void {
    const dh = d[d.len - 1];
    const dl = d[d.len - 2];
    const reciprocal = reciprocal2by1(dh);

    var j: usize = u.len - d.len;
    while (j > 0) {
        j -= 1;

        const u_high = u[j + d.len];
        const u_mid = u[j + d.len - 1];
        const u_low = u[j + d.len - 2];

        var qhat: u64 = 0;
        var rhat: u64 = 0;

        if (u_high >= dh) { 
            qhat = ~@as(u64, 0);
        } else {
            const div_result = udivrem2by1(u_high, u_mid, dh, reciprocal);
            qhat = div_result.quot;
            rhat = div_result.rem;

            const mul = @mulWithOverflow(qhat, dl);
            const ph = mul[1];
            const pl = mul[0];

            if (ph > rhat or (ph == rhat and pl > u_low)) {
                qhat -= 1;
            }
        }

        const borrow = subMulTo(u[j .. j + d.len], d, qhat);
        const u_high_new = u_high -% borrow;
        u[j + d.len] = u_high_new;

        if (u_high < borrow) { 
            qhat -= 1;
            u[j + d.len] +%= addTo(u[j .. j + d.len], d);
        }

        quot[j] = qhat; 
    }
}

/// Divides u by d and produces both quotient and remainder.
/// The quotient is stored in provided quot - len(u)-len(d)+1 words.
/// Loosely follows Knuth's division algorithm (Algorithm D).
pub fn udivrem(quot: []u64, u: []const u64, d: *const U256, rem: ?*U256) void {
    // ~d = 2^64 - 1 - d
    var d_len: usize = 0;
    var i: usize = d.limbs.len;
    while (i > 0) {
        i -= 1;
        if (d.limbs[i] != 0) {
            d_len = i + 1;
            break;
        }
    }

    if (d_len == 0) {
        if (rem) |r| {
            _ = r.clear();
        }
        return;
    }

    const shift: u6 = @intCast(@clz(d.limbs[d_len - 1]));

    var dn_storage: [4]u64 = undefined;
    const dn = dn_storage[0..d_len];

    if (shift > 0) {
        const rshift: u6 = @intCast(64 - @as(u8, shift));
        i = d_len;
        while (i > 1) {
            i -= 1;
            dn[i] = (d.limbs[i] << shift) | (d.limbs[i - 1] >> rshift);
        }
        dn[0] = d.limbs[0] << shift;
    } else {
        @memcpy(dn, d.limbs[0..d_len]);
    }

    var u_len: usize = 0;
    i = u.len;
    while (i > 0) {
        i -= 1;
        if (u[i] != 0) {
            u_len = i + 1;
            break;
        }
    }

    if (u_len < d_len) {
        if (rem) |r| {
            @memcpy(r.limbs[0..u.len], u);
        }
        return;
    }

    var un_storage: [9]u64 = undefined;
    const un = un_storage[0 .. u_len + 1];

    if (shift > 0) {
        const rshift: u6 = @intCast(64 - @as(u8, shift));
        un[u_len] = u[u_len - 1] >> rshift;
        i = u_len;
        while (i > 1) {
            i -= 1;
            un[i] = (u[i] << shift) | (u[i - 1] >> rshift);
        }
        un[0] = u[0] << shift;
    } else {
        @memcpy(un[0..u_len], u[0..u_len]);
        un[u_len] = 0;
    }

    if (d_len == 1) {
        const r = udivremBy1(quot, un, dn[0]);
        if (rem) |r_ptr| {
            r_ptr.limbs[0] = r >> shift;
            r_ptr.limbs[1] = 0;
            r_ptr.limbs[2] = 0;
            r_ptr.limbs[3] = 0;
        }
        return;
    }

    udivremKnuth(quot, un, dn);

    if (rem) |r| {
        if (shift > 0) {
            const lshift: u6 = @intCast(64 - @as(u8, shift));
            i = 0;
            while (i < d_len - 1) : (i += 1) {
                r.limbs[i] = (un[i] >> shift) | (un[i + 1] << lshift);
            }
            r.limbs[d_len - 1] = un[d_len - 1] >> shift;
        } else {
            @memcpy(r.limbs[0..d_len], un[0..d_len]);
        }

        i = d_len;
        while (i < 4) : (i += 1) {
            r.limbs[i] = 0;
        }
    }
}
