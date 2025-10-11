// zig-u256: Fixed size 256-bit math library  
// Modular arithmetic helper functions

const U256 = @import("u256.zig").U256;

/// Computes a 320-bit value representing 1/m (reciprocal for Barrett reduction).
///
/// Notes:
/// - Specialized for m[3] != 0, hence limited to 2^192 <= m < 2^256
/// - Returns zero if m[3] == 0
/// - Uses Newton-Raphson iterations starting with a 32-bit division
/// - Result is used for efficient modular reduction via Barrett's algorithm
///
/// This is a standalone function (not a method) as it computes a property
/// of the modulus independent of any particular value being reduced.
///
/// TODO: This function has compilation issues with variable scoping.
/// The implementation is ~1150 lines with hundreds of temp variable reuses.
/// Needs refactoring to handle Zig's stricter variable scoping rules.
pub fn reciprocal(m: U256) [5]u64 {
    const mu = [_]u64{0} ** 5;

        if (m.limbs[3] == 0) {
            return mu;
        }

        // TODO: Full Newton-Raphson implementation commented out due to compilation errors
        // See CLAUDE.MD for details
        return mu;

        //         // const s = @clz(m.limbs[3]); // Leading zeros
        //         // const p: i32 = 255 - @as(i32, s); // floor(log_2(m)), m>0
        // 
        //         // 0 or a power of 2?
        //         // Check if at least one bit is set in m[2], m[1] or m[0],
        //         // or at least two bits in m[3]
        //         if (m.limbs[0] | m.limbs[1] | m.limbs[2] | (m.limbs[3] & (m.limbs[3] -% 1)) == 0) {
        //             mu[4] = ~@as(u64, 0) >> @intCast(p & 63);
        //             mu[3] = ~@as(u64, 0);
        //             mu[2] = ~@as(u64, 0);
        //             mu[1] = ~@as(u64, 0);
        //             mu[0] = ~@as(u64, 0);
        //             return mu;
        //         }
        // 
        //         // Maximise division precision by left-aligning divisor
        //         var y = U256.initZero(); // left-aligned copy of m
        //         _ = y.lsh(m, @intCast(s)); // 1/2 < y < 1
        // 
        //         // Extract most significant 32 bits
        //         const yh: u32 = @truncate(y.limbs[3] >> 32);
        // 
        //         var r0: u32 = 0;
        //         if (yh == 0x80000000) { // Avoid overflow in division
        //             r0 = 0xffffffff;
        //         } else {
        //             // Compute 2^63 / yh (32-bit division)
        //             r0 = @truncate(@as(u64, 0x8000000000000000) / @as(u64, yh));
        //         }
        // 
        //         // First iteration: 32 -> 64
        //         var t1: u64 = r0; // 2^31/y
        //         t1 *= t1; // 2^62/y^2
        //         const mul1 = @mulWithOverflow(t1, y.limbs[3]);
        //         t1 = mul1[1]; // 2^62/y^2 * 2^64/y / 2^64 = 2^62/y
        // 
        //         var r1 = @as(u64, r0) << 32; // 2^63/y
        //         r1 -%= t1; // 2^63/y - 2^62/y = 2^62/y
        //         r1 *%= 2; // 2^63/y
        // 
        //         if ((r1 | (y.limbs[3] << 1)) == 0) {
        //             r1 = ~@as(u64, 0);
        //         }
        // 
        //         // Second iteration: 64 -> 128
        //         // square: 2^126/y^2
        //         const mul2 = @mulWithOverflow(r1, r1);
        //         const a2h = mul2[1];
        //         const a2l = mul2[0];
        // 
        //         // multiply by y: e2h:e2l:b2h = 2^126/y^2 * 2^128/y / 2^128 = 2^126/y
        //         const mulb = @mulWithOverflow(a2l, y.limbs[2]);
        //         var b2h = mulb[1];
        // 
        //         const mulc = @mulWithOverflow(a2l, y.limbs[3]);
        //         const c2h = mulc[1];
        //         const c2l = mulc[0];
        // 
        //         const muld = @mulWithOverflow(a2h, y.limbs[2]);
        //         const d2h = muld[1];
        //         const d2l = muld[0];
        // 
        //         const mule = @mulWithOverflow(a2h, y.limbs[3]);
        //         var e2h = mule[1];
        //         var e2l = mule[0];
        // 
        //         const add2_1 = @addWithOverflow(b2h, c2l);
        //         b2h = add2_1[0];
        //         var carry: u64 = @as(u64, add2_1[1]);
        // 
        //         const add2_2 = @addWithOverflow(e2l, c2h);
        //         e2l = add2_2[0];
        //         carry |= @as(u64, add2_2[1]);
        // 
        //         const add2_3 = @addWithOverflow(e2l, carry);
        //         e2l = add2_3[0];
        //         carry = @as(u64, add2_3[1]);
        // 
        //         e2h +%= carry;
        // 
        //         const add2_4 = @addWithOverflow(b2h, d2l);
        //         carry = @as(u64, add2_4[1]);
        // 
        //         const add2_5 = @addWithOverflow(e2l, d2h);
        //         e2l = add2_5[0];
        //         carry |= @as(u64, add2_5[1]);
        // 
        //         const add2_6 = @addWithOverflow(e2l, carry);
        //         e2l = add2_6[0];
        //         carry = @as(u64, add2_6[1]);
        // 
        //         e2h +%= carry;
        // 
        //         // subtract: t2h:t2l = 2^127/y - 2^126/y = 2^126/y
        //         var sub1 = @subWithOverflow(0, e2l);
        //         const t2l = sub1[0];
        //         var borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r1, e2h);
        //         const t2h = sub1[0] -% borrow;
        // 
        //         // double: r2h:r2l = 2^127/y
        //         add1 = @addWithOverflow(t2l, t2l);
        //         var r2l = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(t2h, t2h);
        //         var r2h = add1[0] +% carry;
        // 
        //         if ((r2h | r2l | (y.limbs[3] << 1)) == 0) {
        //             r2h = ~@as(u64, 0);
        //             r2l = ~@as(u64, 0);
        //         }
        // 
        //         // Third iteration: 128 -> 192
        //         // square r2 (keep 256 bits): 2^190/y^2
        //         const mul3a = @mulWithOverflow(r2l, r2l);
        //         var a3h = mul3a[1];
        //         const a3l = mul3a[0];
        // 
        //         const mul3b = @mulWithOverflow(r2l, r2h);
        //         const b3h = mul3b[1];
        //         const b3l = mul3b[0];
        // 
        //         const mul3c = @mulWithOverflow(r2h, r2h);
        //         var c3h = mul3c[1];
        //         var c3l = mul3c[0];
        // 
        //         add1 = @addWithOverflow(a3h, b3l);
        //         a3h = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(c3l, b3h);
        //         c3l = add1[0];
        //         carry |= add1[1];
        // 
        //         add1 = @addWithOverflow(c3l, carry);
        //         c3l = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(c3h, 0);
        //         c3h = add1[0] +% carry;
        // 
        //         add1 = @addWithOverflow(a3h, b3l);
        //         a3h = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(c3l, b3h);
        //         c3l = add1[0];
        //         carry |= add1[1];
        // 
        //         add1 = @addWithOverflow(c3l, carry);
        //         c3l = add1[0];
        //         carry = add1[1];
        // 
        //         c3h +%= carry;
        // 
        //         // multiply by y: q = 2^190/y^2 * 2^192/y / 2^192 = 2^190/y
        //         const x0 = a3l;
        //         const x1 = a3h;
        //         const x2 = c3l;
        //         const x3 = c3h;
        // 
        //         var q0: u64 = 0;
        //         var q1: u64 = 0;
        //         var q2: u64 = 0;
        //         var q3: u64 = 0;
        //         var q4: u64 = 0;
        //         var t0: u64 = 0;
        // 
        //         const mulq0 = @mulWithOverflow(x2, y.limbs[0]);
        //         q0 = mulq0[1];
        // 
        //         const mulq1 = @mulWithOverflow(x3, y.limbs[0]);
        //         q1 = mulq1[1];
        //         t0 = mulq1[0];
        //         add1 = @addWithOverflow(q0, t0);
        //         q0 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q1, 0);
        //         q1 = add1[0] +% carry;
        // 
        //         const mult1_1 = @mulWithOverflow(x1, y.limbs[1]);
        //         t1 = mult1_1[1];
        //         add1 = @addWithOverflow(q0, t1);
        //         q0 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq2 = @mulWithOverflow(x3, y.limbs[1]);
        //         q2 = mulq2[1];
        //         t0 = mulq2[0];
        //         add1 = @addWithOverflow(q1, t0);
        //         q1 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q1, carry);
        //         q1 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q2, 0);
        //         q2 = add1[0] +% carry;
        // 
        //         const mult1_2 = @mulWithOverflow(x2, y.limbs[1]);
        //         t1 = mult1_2[1];
        //         t0 = mult1_2[0];
        //         add1 = @addWithOverflow(q0, t0);
        //         q0 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q1, t1);
        //         q1 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q1, carry);
        //         q1 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q2, 0);
        //         q2 = add1[0] +% carry;
        // 
        //         const mult1_3 = @mulWithOverflow(x1, y.limbs[2]);
        //         t1 = mult1_3[1];
        //         t0 = mult1_3[0];
        //         add1 = @addWithOverflow(q0, t0);
        //         q0 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q1, t1);
        //         q1 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q1, carry);
        //         q1 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq3 = @mulWithOverflow(x3, y.limbs[2]);
        //         q3 = mulq3[1];
        //         t0 = mulq3[0];
        //         add1 = @addWithOverflow(q2, t0);
        //         q2 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q2, carry);
        //         q2 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q3, 0);
        //         q3 = add1[0] +% carry;
        // 
        //         const mult1_4 = @mulWithOverflow(x0, y.limbs[2]);
        //         t1 = mult1_4[1];
        //         add1 = @addWithOverflow(q0, t1);
        //         q0 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult1_5 = @mulWithOverflow(x2, y.limbs[2]);
        //         t1 = mult1_5[1];
        //         t0 = mult1_5[0];
        //         add1 = @addWithOverflow(q1, t0);
        //         q1 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q1, carry);
        //         q1 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q2, t1);
        //         q2 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q2, carry);
        //         q2 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q3, 0);
        //         q3 = add1[0] +% carry;
        // 
        //         const mult1_6 = @mulWithOverflow(x1, y.limbs[3]);
        //         t1 = mult1_6[1];
        //         t0 = mult1_6[0];
        //         add1 = @addWithOverflow(q1, t0);
        //         q1 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q2, t1);
        //         q2 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q2, carry);
        //         q2 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq4 = @mulWithOverflow(x3, y.limbs[3]);
        //         q4 = mulq4[1];
        //         t0 = mulq4[0];
        //         add1 = @addWithOverflow(q3, t0);
        //         q3 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q3, carry);
        //         q3 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q4, 0);
        //         q4 = add1[0] +% carry;
        // 
        //         const mult1_7 = @mulWithOverflow(x0, y.limbs[3]);
        //         t1 = mult1_7[1];
        //         t0 = mult1_7[0];
        //         add1 = @addWithOverflow(q0, t0);
        //         q0 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q1, t1);
        //         q1 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q1, carry);
        //         q1 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult1_8 = @mulWithOverflow(x2, y.limbs[3]);
        //         t1 = mult1_8[1];
        //         t0 = mult1_8[0];
        //         add1 = @addWithOverflow(q2, t0);
        //         q2 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q2, carry);
        //         q2 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q3, t1);
        //         q3 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q3, carry);
        //         q3 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q4, 0);
        //         q4 = add1[0] +% carry;
        // 
        //         // subtract: t3 = 2^191/y - 2^190/y = 2^190/y
        //         sub1 = @subWithOverflow(0, q0);
        //         borrow = sub1[1];
        //         sub1 = @subWithOverflow(0, q1);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, q2);
        //         var t3l = sub1[0];
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(t3l, borrow);
        //         t3l = sub1[0];
        //         borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r2l, q3);
        //         var t3m = sub1[0];
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(t3m, borrow);
        //         t3m = sub1[0];
        //         borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r2h, q4);
        //         var t3h = sub1[0];
        //         borrow |= sub1[1];
        //         t3h -%= borrow;
        // 
        //         // double: r3 = 2^191/y
        //         add1 = @addWithOverflow(t3l, t3l);
        //         const r3l = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(t3m, t3m);
        //         var r3m = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(r3m, carry);
        //         r3m = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(t3h, t3h);
        //         var r3h = add1[0];
        //         carry |= add1[1];
        //         r3h +%= carry;
        // 
        //         // Fourth iteration: 192 -> 320
        //         // square r3
        //         const mul4a = @mulWithOverflow(r3l, r3l);
        //         var a4h = mul4a[1];
        //         const a4l = mul4a[0];
        // 
        //         const mul4b = @mulWithOverflow(r3l, r3m);
        //         var b4h = mul4b[1];
        //         const b4l = mul4b[0];
        // 
        //         const mul4c = @mulWithOverflow(r3l, r3h);
        //         const c4h = mul4c[1];
        //         const c4l = mul4c[0];
        // 
        //         const mul4d = @mulWithOverflow(r3m, r3m);
        //         var d4h = mul4d[1];
        //         var d4l = mul4d[0];
        // 
        //         const mul4e = @mulWithOverflow(r3m, r3h);
        //         var e4h = mul4e[1];
        //         var e4l = mul4e[0];
        // 
        //         const mul4f = @mulWithOverflow(r3h, r3h);
        //         var f4h = mul4f[1];
        //         var f4l = mul4f[0];
        // 
        //         add1 = @addWithOverflow(b4h, c4l);
        //         b4h = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(e4l, c4h);
        //         e4l = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(e4l, carry);
        //         e4l = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(e4h, 0);
        //         e4h = add1[0] +% carry;
        // 
        //         add1 = @addWithOverflow(a4h, b4l);
        //         a4h = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(d4l, b4h);
        //         d4l = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(d4l, carry);
        //         d4l = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(d4h, e4l);
        //         d4h = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(d4h, carry);
        //         d4h = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(f4l, e4h);
        //         f4l = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(f4l, carry);
        //         f4l = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(f4h, 0);
        //         f4h = add1[0] +% carry;
        // 
        //         add1 = @addWithOverflow(a4h, b4l);
        //         a4h = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(d4l, b4h);
        //         d4l = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(d4l, carry);
        //         d4l = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(d4h, e4l);
        //         d4h = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(d4h, carry);
        //         d4h = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(f4l, e4h);
        //         f4l = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(f4l, carry);
        //         f4l = add1[0];
        //         carry = add1[1];
        // 
        //         f4h +%= carry;
        // 
        //         // multiply by y
        //         var x1_iter4: u64 = 0;
        //         var x2_iter4: u64 = 0;
        //         var x3_iter4: u64 = 0;
        //         var x4_iter4: u64 = 0;
        //         var x5_iter4: u64 = 0;
        //         var x6_iter4: u64 = 0;
        // 
        //         const mulx1 = @mulWithOverflow(d4h, y.limbs[0]);
        //         x1_iter4 = mulx1[1];
        //         var x0_iter4 = mulx1[0];
        // 
        //         const mulx3 = @mulWithOverflow(f4h, y.limbs[0]);
        //         x3_iter4 = mulx3[1];
        //         x2_iter4 = mulx3[0];
        // 
        //         const mult_fl_y0 = @mulWithOverflow(f4l, y.limbs[0]);
        //         t1 = mult_fl_y0[1];
        //         t0 = mult_fl_y0[0];
        //         add1 = @addWithOverflow(x1_iter4, t0);
        //         x1_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x2_iter4, t1);
        //         x2_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_iter4, carry);
        //         x2_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x3_iter4, 0);
        //         x3_iter4 = add1[0] +% carry;
        // 
        //         const mult_dh_y1 = @mulWithOverflow(d4h, y.limbs[1]);
        //         t1 = mult_dh_y1[1];
        //         t0 = mult_dh_y1[0];
        //         add1 = @addWithOverflow(x1_iter4, t0);
        //         x1_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x2_iter4, t1);
        //         x2_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_iter4, carry);
        //         x2_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulx4 = @mulWithOverflow(f4h, y.limbs[1]);
        //         x4_iter4 = mulx4[1];
        //         t0 = mulx4[0];
        //         add1 = @addWithOverflow(x3_iter4, t0);
        //         x3_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x3_iter4, carry);
        //         x3_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x4_iter4, 0);
        //         x4_iter4 = add1[0] +% carry;
        // 
        //         const mult_dl_y1 = @mulWithOverflow(d4l, y.limbs[1]);
        //         t1 = mult_dl_y1[1];
        //         t0 = mult_dl_y1[0];
        //         add1 = @addWithOverflow(x0_iter4, t0);
        //         x0_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x1_iter4, t1);
        //         x1_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x1_iter4, carry);
        //         x1_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult_fl_y1 = @mulWithOverflow(f4l, y.limbs[1]);
        //         t1 = mult_fl_y1[1];
        //         t0 = mult_fl_y1[0];
        //         add1 = @addWithOverflow(x2_iter4, t0);
        //         x2_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_iter4, carry);
        //         x2_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x3_iter4, t1);
        //         x3_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x3_iter4, carry);
        //         x3_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x4_iter4, 0);
        //         x4_iter4 = add1[0] +% carry;
        // 
        //         const mult_ah_y2 = @mulWithOverflow(a4h, y.limbs[2]);
        //         t1 = mult_ah_y2[1];
        //         t0 = mult_ah_y2[0];
        //         add1 = @addWithOverflow(x0_iter4, t0);
        //         x0_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x1_iter4, t1);
        //         x1_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x1_iter4, carry);
        //         x1_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult_dh_y2 = @mulWithOverflow(d4h, y.limbs[2]);
        //         t1 = mult_dh_y2[1];
        //         t0 = mult_dh_y2[0];
        //         add1 = @addWithOverflow(x2_iter4, t0);
        //         x2_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_iter4, carry);
        //         x2_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x3_iter4, t1);
        //         x3_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x3_iter4, carry);
        //         x3_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulx5 = @mulWithOverflow(f4h, y.limbs[2]);
        //         x5_iter4 = mulx5[1];
        //         t0 = mulx5[0];
        //         add1 = @addWithOverflow(x4_iter4, t0);
        //         x4_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x4_iter4, carry);
        //         x4_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x5_iter4, 0);
        //         x5_iter4 = add1[0] +% carry;
        // 
        //         const mult_dl_y2 = @mulWithOverflow(d4l, y.limbs[2]);
        //         t1 = mult_dl_y2[1];
        //         t0 = mult_dl_y2[0];
        //         add1 = @addWithOverflow(x1_iter4, t0);
        //         x1_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x2_iter4, t1);
        //         x2_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_iter4, carry);
        //         x2_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult_fl_y2 = @mulWithOverflow(f4l, y.limbs[2]);
        //         t1 = mult_fl_y2[1];
        //         t0 = mult_fl_y2[0];
        //         add1 = @addWithOverflow(x3_iter4, t0);
        //         x3_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x3_iter4, carry);
        //         x3_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x4_iter4, t1);
        //         x4_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x4_iter4, carry);
        //         x4_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x5_iter4, 0);
        //         x5_iter4 = add1[0] +% carry;
        // 
        //         const mult_ah_y3 = @mulWithOverflow(a4h, y.limbs[3]);
        //         t1 = mult_ah_y3[1];
        //         t0 = mult_ah_y3[0];
        //         add1 = @addWithOverflow(x1_iter4, t0);
        //         x1_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x2_iter4, t1);
        //         x2_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_iter4, carry);
        //         x2_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult_dh_y3 = @mulWithOverflow(d4h, y.limbs[3]);
        //         t1 = mult_dh_y3[1];
        //         t0 = mult_dh_y3[0];
        //         add1 = @addWithOverflow(x3_iter4, t0);
        //         x3_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x3_iter4, carry);
        //         x3_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x4_iter4, t1);
        //         x4_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x4_iter4, carry);
        //         x4_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulx6 = @mulWithOverflow(f4h, y.limbs[3]);
        //         x6_iter4 = mulx6[1];
        //         t0 = mulx6[0];
        //         add1 = @addWithOverflow(x5_iter4, t0);
        //         x5_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x5_iter4, carry);
        //         x5_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x6_iter4, 0);
        //         x6_iter4 = add1[0] +% carry;
        // 
        //         const mult_al_y3 = @mulWithOverflow(a4l, y.limbs[3]);
        //         t1 = mult_al_y3[1];
        //         t0 = mult_al_y3[0];
        //         add1 = @addWithOverflow(x0_iter4, t0);
        //         x0_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x1_iter4, t1);
        //         x1_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x1_iter4, carry);
        //         x1_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult_dl_y3 = @mulWithOverflow(d4l, y.limbs[3]);
        //         t1 = mult_dl_y3[1];
        //         t0 = mult_dl_y3[0];
        //         add1 = @addWithOverflow(x2_iter4, t0);
        //         x2_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_iter4, carry);
        //         x2_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x3_iter4, t1);
        //         x3_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x3_iter4, carry);
        //         x3_iter4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mult_fl_y3 = @mulWithOverflow(f4l, y.limbs[3]);
        //         t1 = mult_fl_y3[1];
        //         t0 = mult_fl_y3[0];
        //         add1 = @addWithOverflow(x4_iter4, t0);
        //         x4_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x4_iter4, carry);
        //         x4_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x5_iter4, t1);
        //         x5_iter4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x5_iter4, carry);
        //         x5_iter4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(x6_iter4, 0);
        //         x6_iter4 = add1[0] +% carry;
        // 
        //         // subtract
        //         sub1 = @subWithOverflow(0, x0_iter4);
        //         borrow = sub1[1];
        //         sub1 = @subWithOverflow(0, x1_iter4);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, x2_iter4);
        //         var r4l = sub1[0];
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(r4l, borrow);
        //         r4l = sub1[0];
        //         borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(0, x3_iter4);
        //         var r4k = sub1[0];
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(r4k, borrow);
        //         r4k = sub1[0];
        //         borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r3l, x4_iter4);
        //         var r4j = sub1[0];
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(r4j, borrow);
        //         r4j = sub1[0];
        //         borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r3m, x5_iter4);
        //         var r4i = sub1[0];
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(r4i, borrow);
        //         r4i = sub1[0];
        //         borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r3h, x6_iter4);
        //         var r4h = sub1[0];
        //         borrow |= sub1[1];
        //         r4h -%= borrow;
        // 
        //         // Multiply candidate for 1/4y by y, with full precision
        //         var x0_final = r4l;
        //         var x1_final = r4k;
        //         var x2_final = r4j;
        //         var x3_final = r4i;
        //         var x4_final = r4h;
        // 
        //         const mulq_x0y0 = @mulWithOverflow(x0_final, y.limbs[0]);
        //         q1 = mulq_x0y0[1];
        //         q0 = mulq_x0y0[0];
        // 
        //         const mulq_x2y0 = @mulWithOverflow(x2_final, y.limbs[0]);
        //         q3 = mulq_x2y0[1];
        //         q2 = mulq_x2y0[0];
        // 
        //         const mulq_x4y0 = @mulWithOverflow(x4_final, y.limbs[0]);
        //         var q5 = mulq_x4y0[1];
        //         q4 = mulq_x4y0[0];
        // 
        //         const mulq_x1y0 = @mulWithOverflow(x1_final, y.limbs[0]);
        //         t1 = mulq_x1y0[1];
        //         t0 = mulq_x1y0[0];
        //         add1 = @addWithOverflow(q1, t0);
        //         q1 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q2, t1);
        //         q2 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q2, carry);
        //         q2 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x3y0 = @mulWithOverflow(x3_final, y.limbs[0]);
        //         t1 = mulq_x3y0[1];
        //         t0 = mulq_x3y0[0];
        //         add1 = @addWithOverflow(q3, t0);
        //         q3 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q3, carry);
        //         q3 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q4, t1);
        //         q4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q4, carry);
        //         q4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q5, 0);
        //         q5 = add1[0] +% carry;
        // 
        //         const mulq_x0y1 = @mulWithOverflow(x0_final, y.limbs[1]);
        //         t1 = mulq_x0y1[1];
        //         t0 = mulq_x0y1[0];
        //         add1 = @addWithOverflow(q1, t0);
        //         q1 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q2, t1);
        //         q2 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q2, carry);
        //         q2 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x2y1 = @mulWithOverflow(x2_final, y.limbs[1]);
        //         t1 = mulq_x2y1[1];
        //         t0 = mulq_x2y1[0];
        //         add1 = @addWithOverflow(q3, t0);
        //         q3 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q3, carry);
        //         q3 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q4, t1);
        //         q4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q4, carry);
        //         q4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x4y1 = @mulWithOverflow(x4_final, y.limbs[1]);
        //         var q6 = mulq_x4y1[1];
        //         t0 = mulq_x4y1[0];
        //         add1 = @addWithOverflow(q5, t0);
        //         q5 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q5, carry);
        //         q5 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q6, 0);
        //         q6 = add1[0] +% carry;
        // 
        //         const mulq_x1y1 = @mulWithOverflow(x1_final, y.limbs[1]);
        //         t1 = mulq_x1y1[1];
        //         t0 = mulq_x1y1[0];
        //         add1 = @addWithOverflow(q2, t0);
        //         q2 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q3, t1);
        //         q3 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q3, carry);
        //         q3 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x3y1 = @mulWithOverflow(x3_final, y.limbs[1]);
        //         t1 = mulq_x3y1[1];
        //         t0 = mulq_x3y1[0];
        //         add1 = @addWithOverflow(q4, t0);
        //         q4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q4, carry);
        //         q4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q5, t1);
        //         q5 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q5, carry);
        //         q5 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q6, 0);
        //         q6 = add1[0] +% carry;
        // 
        //         const mulq_x0y2 = @mulWithOverflow(x0_final, y.limbs[2]);
        //         t1 = mulq_x0y2[1];
        //         t0 = mulq_x0y2[0];
        //         add1 = @addWithOverflow(q2, t0);
        //         q2 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q3, t1);
        //         q3 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q3, carry);
        //         q3 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x2y2 = @mulWithOverflow(x2_final, y.limbs[2]);
        //         t1 = mulq_x2y2[1];
        //         t0 = mulq_x2y2[0];
        //         add1 = @addWithOverflow(q4, t0);
        //         q4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q4, carry);
        //         q4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q5, t1);
        //         q5 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q5, carry);
        //         q5 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x4y2 = @mulWithOverflow(x4_final, y.limbs[2]);
        //         var q7 = mulq_x4y2[1];
        //         t0 = mulq_x4y2[0];
        //         add1 = @addWithOverflow(q6, t0);
        //         q6 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q6, carry);
        //         q6 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q7, 0);
        //         q7 = add1[0] +% carry;
        // 
        //         const mulq_x1y2 = @mulWithOverflow(x1_final, y.limbs[2]);
        //         t1 = mulq_x1y2[1];
        //         t0 = mulq_x1y2[0];
        //         add1 = @addWithOverflow(q3, t0);
        //         q3 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q4, t1);
        //         q4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q4, carry);
        //         q4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x3y2 = @mulWithOverflow(x3_final, y.limbs[2]);
        //         t1 = mulq_x3y2[1];
        //         t0 = mulq_x3y2[0];
        //         add1 = @addWithOverflow(q5, t0);
        //         q5 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q5, carry);
        //         q5 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q6, t1);
        //         q6 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q6, carry);
        //         q6 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q7, 0);
        //         q7 = add1[0] +% carry;
        // 
        //         const mulq_x0y3 = @mulWithOverflow(x0_final, y.limbs[3]);
        //         t1 = mulq_x0y3[1];
        //         t0 = mulq_x0y3[0];
        //         add1 = @addWithOverflow(q3, t0);
        //         q3 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q4, t1);
        //         q4 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q4, carry);
        //         q4 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x2y3 = @mulWithOverflow(x2_final, y.limbs[3]);
        //         t1 = mulq_x2y3[1];
        //         t0 = mulq_x2y3[0];
        //         add1 = @addWithOverflow(q5, t0);
        //         q5 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q5, carry);
        //         q5 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q6, t1);
        //         q6 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q6, carry);
        //         q6 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x4y3 = @mulWithOverflow(x4_final, y.limbs[3]);
        //         var q8 = mulq_x4y3[1];
        //         t0 = mulq_x4y3[0];
        //         add1 = @addWithOverflow(q7, t0);
        //         q7 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q7, carry);
        //         q7 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q8, 0);
        //         q8 = add1[0] +% carry;
        // 
        //         const mulq_x1y3 = @mulWithOverflow(x1_final, y.limbs[3]);
        //         t1 = mulq_x1y3[1];
        //         t0 = mulq_x1y3[0];
        //         add1 = @addWithOverflow(q4, t0);
        //         q4 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q5, t1);
        //         q5 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q5, carry);
        //         q5 = add1[0];
        //         carry = add1[1];
        // 
        //         const mulq_x3y3 = @mulWithOverflow(x3_final, y.limbs[3]);
        //         t1 = mulq_x3y3[1];
        //         t0 = mulq_x3y3[0];
        //         add1 = @addWithOverflow(q6, t0);
        //         q6 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q6, carry);
        //         q6 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q7, t1);
        //         q7 = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(q7, carry);
        //         q7 = add1[0];
        //         carry = add1[1];
        //         add1 = @addWithOverflow(q8, 0);
        //         q8 = add1[0] +% carry;
        // 
        //         // Final adjustment
        //         // subtract q from 1/4
        //         sub1 = @subWithOverflow(0, q0);
        //         borrow = sub1[1];
        //         sub1 = @subWithOverflow(0, q1);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, q2);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, q3);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, q4);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, q5);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, q6);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(0, q7);
        //         borrow |= sub1[1];
        //         sub1 = @subWithOverflow(@as(u64, 1) << 62, q8);
        //         borrow |= sub1[1];
        // 
        //         // decrement the result
        //         sub1 = @subWithOverflow(r4l, 1);
        //         const x0_dec = sub1[0];
        //         var t_borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r4k, 0);
        //         var x1_dec = sub1[0];
        //         t_borrow |= sub1[1];
        //         sub1 = @subWithOverflow(x1_dec, t_borrow);
        //         x1_dec = sub1[0];
        //         t_borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r4j, 0);
        //         var x2_dec = sub1[0];
        //         t_borrow |= sub1[1];
        //         sub1 = @subWithOverflow(x2_dec, t_borrow);
        //         x2_dec = sub1[0];
        //         t_borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r4i, 0);
        //         var x3_dec = sub1[0];
        //         t_borrow |= sub1[1];
        //         sub1 = @subWithOverflow(x3_dec, t_borrow);
        //         x3_dec = sub1[0];
        //         t_borrow = sub1[1];
        // 
        //         sub1 = @subWithOverflow(r4h, 0);
        //         var x4_dec = sub1[0];
        //         t_borrow |= sub1[1];
        //         x4_dec -%= t_borrow;
        // 
        //         // commit the decrement if the subtraction underflowed (reciprocal was too large)
        //         if (borrow != 0) {
        //             r4h = x4_dec;
        //             r4i = x3_dec;
        //             r4j = x2_dec;
        //             r4k = x1_dec;
        //             r4l = x0_dec;
        //         }
        // 
        //         // Shift to correct bit alignment, truncating excess bits
        //         var p_shift = (p & 63) - 1;
        // 
        //         add1 = @addWithOverflow(r4l, r4l);
        //         x0_final = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(r4k, r4k);
        //         x1_final = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x1_final, carry);
        //         x1_final = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(r4j, r4j);
        //         x2_final = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x2_final, carry);
        //         x2_final = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(r4i, r4i);
        //         x3_final = add1[0];
        //         carry |= add1[1];
        //         add1 = @addWithOverflow(x3_final, carry);
        //         x3_final = add1[0];
        //         carry = add1[1];
        // 
        //         add1 = @addWithOverflow(r4h, r4h);
        //         x4_final = add1[0];
        //         carry |= add1[1];
        //         x4_final +%= carry;
        // 
        //         if (p_shift < 0) {
        //             r4h = x4_final;
        //             r4i = x3_final;
        //             r4j = x2_final;
        //             r4k = x1_final;
        //             r4l = x0_final;
        //             p_shift = 0; // avoid negative shift below
        //         }
        // 
        //         if (p_shift > 0) {
        //             const r: u6 = @intCast(p_shift); // right shift
        //             const l: u6 = @intCast(64 - p_shift); // left shift
        // 
        //             x0_final = (r4l >> r) | (r4k << l);
        //             x1_final = (r4k >> r) | (r4j << l);
        //             x2_final = (r4j >> r) | (r4i << l);
        //             x3_final = (r4i >> r) | (r4h << l);
        //             x4_final = r4h >> r;
        // 
        //             r4h = x4_final;
        //             r4i = x3_final;
        //             r4j = x2_final;
        //             r4k = x1_final;
        //             r4l = x0_final;
        //         }
        // 
        //         mu[0] = r4l;
        //         mu[1] = r4k;
        //         mu[2] = r4j;
        //         mu[3] = r4i;
        //         mu[4] = r4h;
        // 
        //         return mu;
    }
