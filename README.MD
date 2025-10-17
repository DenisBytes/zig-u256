# zig-u256

A 256-bit unsigned integer library for Zig.

## Status

⚠️ **This library is in beta** - several functions are not yet working correctly. See the [Known Issues](#known-issues) section below.

## Overview

Zig implementation of 256-bit unsigned integers, inspired by the Go [uint256](https://github.com/holiman/uint256) library.

### Features

- **Zero allocations** - All operations are stack-allocated (except decimal string formatting which uses `std.math.big.Int` requiring an allocator)
- **Fixed 4×64-bit limb structure** - Optimized for performance and EVM compatibility
- **Blockchain-focused** - Implements EVM-specific operations like `SIGNEXTEND`

## Usage

Add as a dependency in your `build.zig.zon` and import:

```zig
const U256 = @import("zig_u256").U256;

const a = U256.init(42);
var b = U256.initZero();
_ = b.setBytes(&[_]u8{ 0x01, 0x02, 0x03, 0x04 });
```

## Building

```bash
zig build test
```

## Known Issues

The following functions are currently **not working correctly**:

### Modular Arithmetic
- `mod` - Incorrect results for large values
- `imod` - Incorrect results for large values
- `addMod` - Fails with 256-bit overflow
- `iaddMod` - Incorrect overflow handling
- `mulDivOverflow` - Incorrect calculation results

### String Formatting & Parsing
- `dec` - Decimal string formatting issues
- `prettyDec` - Pretty decimal formatting issues
- `hex` - Hexadecimal string formatting issues
- `format` - Generic formatting issues
- `scan` - Missing overflow detection

### Low-Level Operations
- `udivrem` - Not properly implemented
- `reciprocal` - Not properly implemented

These issues are being actively worked on. Contributions welcome!

## License

MIT
