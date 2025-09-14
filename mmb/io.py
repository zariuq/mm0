"""Binary readers for the MMB format."""
from __future__ import annotations


class BR:
    """A bounded reader over a bytes object.

    Mirrors `mm0-rs/components/mm0b_parser/src/lib.rs` basic parsing helpers.
    """

    def __init__(self, data: bytes):
        self.b = memoryview(data)
        self.i = 0
        self.n = len(data)

    def take(self, k: int) -> memoryview:
        if k < 0 or self.i + k > self.n:
            raise ValueError("short read")
        s = self.b[self.i : self.i + k]
        self.i += k
        return s

    def u8(self) -> int:
        return int(self.take(1)[0])

    def u32(self) -> int:
        import struct

        (x,) = struct.unpack_from("<I", self.take(4))
        return x

    def u64(self) -> int:
        import struct

        (x,) = struct.unpack_from("<Q", self.take(8))
        return x

    def varu(self) -> int:
        """Read an unsigned LEB128 integer."""
        x = 0
        shift = 0
        while True:
            b = self.u8()
            x |= (b & 0x7F) << shift
            if b < 0x80:
                return x
            shift += 7
            if shift > 63:
                raise ValueError("varu overflow")


