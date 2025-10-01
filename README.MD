# zig-u256

A 256 unsigned integer library for Zig.

## Overview

Zig implementation of 256 unsigned integers, inspired by the Go [uint256](https://github.com/holiman/uint256) library.

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

## License

MIT
