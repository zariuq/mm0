import pathlib
import subprocess
import shutil
import sys
import pytest

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT))

from mmb.format import load_mmb


def ensure_mm0c() -> str:
    mm0c = shutil.which("mm0-c")
    if mm0c:
        return mm0c
    mm0c_path = ROOT / "mm0-c" / "mm0-c"
    if mm0c_path.exists():
        return str(mm0c_path)
    gcc = shutil.which("gcc")
    if gcc is None:
        pytest.skip("gcc not available to build mm0-c")
    subprocess.run([gcc, str(ROOT / "mm0-c" / "main.c"), "-O2", "-o", str(mm0c_path)], check=True)
    return str(mm0c_path)


def ensure_peano_mmb() -> pathlib.Path:
    path = ROOT / "examples" / "peano.mmb"
    mm0c = ensure_mm0c()
    if path.exists():
        with open(ROOT / "examples" / "peano.mm0", "rb") as mm0_file:
            if subprocess.run([mm0c, str(path)], stdin=mm0_file).returncode == 0:
                return path
    mm0hs = shutil.which("mm0-hs")
    if mm0hs is not None:
        subprocess.run(
            [mm0hs, "export", str(ROOT / "examples" / "peano.mmu"), "-o", str(path)],
            check=True,
        )
        with open(ROOT / "examples" / "peano.mm0", "rb") as mm0_file:
            if subprocess.run([mm0c, str(path)], stdin=mm0_file).returncode == 0:
                return path
    mm0rs = shutil.which("mm0-rs")
    if mm0rs is not None:
        subprocess.run(
            [mm0rs, "compile", str(ROOT / "examples" / "peano.mm1"), str(path)],
            check=True,
        )
        return path
    pytest.skip("no tool to build peano.mmb")


def test_mmb_valid():
    mm0c = ensure_mm0c()
    mm0_path = ROOT / "examples" / "peano.mm0"
    mmb_path = ensure_peano_mmb()
    with open(mm0_path, "rb") as mm0_file:
        subprocess.run([mm0c, str(mmb_path)], stdin=mm0_file, check=True)
    load_mmb(mmb_path.read_bytes(), strict_align=False)


def mutate_bad_magic(b: bytes) -> bytes:
    bb = bytearray(b)
    bb[0:4] = b"BAD!"
    return bytes(bb)


def mutate_version(b: bytes) -> bytes:
    bb = bytearray(b)
    bb[4] = 2
    return bytes(bb)


def mutate_misordered(b: bytes) -> bytes:
    bb = bytearray(b)
    p_terms = int.from_bytes(bb[16:20], "little")
    bb[20:24] = (p_terms - 4).to_bytes(4, "little")
    return bytes(bb)


def mutate_pindex(b: bytes) -> bytes:
    bb = bytearray(b)
    bb[32:40] = (len(bb) + 1).to_bytes(8, "little")
    return bytes(bb)


def mutate_malformed_name(b: bytes) -> bytes:
    bb = bytearray(b)
    p_index = int.from_bytes(bb[32:40], "little")
    i = p_index + 8
    while i + 16 <= len(bb):
        if bytes(bb[i:i+4]) == b"Name":
            bb[i+8:i+16] = (len(bb) - 8).to_bytes(8, "little")
            break
        i += 16
    return bytes(bb)


def mutate_name_ptr_oob(b: bytes) -> bytes:
    bb = bytearray(b)
    p_index = int.from_bytes(bb[32:40], "little")
    i = p_index + 8
    name_ptr = None
    while i + 16 <= len(bb):
        if bytes(bb[i:i+4]) == b"Name":
            name_ptr = int.from_bytes(bb[i+8:i+16], "little")
            break
        i += 16
    if name_ptr is not None:
        bb[name_ptr+8:name_ptr+16] = (len(bb) + 1).to_bytes(8, "little")
    return bytes(bb)


def mutate_unterminated_string(b: bytes) -> bytes:
    bb = bytearray(b)
    p_index = int.from_bytes(bb[32:40], "little")
    i = p_index + 8
    name_ptr = None
    while i + 16 <= len(bb):
        if bytes(bb[i:i+4]) == b"Name":
            name_ptr = int.from_bytes(bb[i+8:i+16], "little")
            break
        i += 16
    if name_ptr is not None:
        bb[name_ptr+8:name_ptr+16] = (len(bb) - 1).to_bytes(8, "little")
        if bb[-1] == 0:
            bb[-1] = 1
    return bytes(bb)


@pytest.mark.parametrize(
    "name,mut,category",
    [
        ("bad_magic", mutate_bad_magic, "structural"),
        ("version", mutate_version, "structural"),
        ("misordered", mutate_misordered, "structural"),
        ("p_index", mutate_pindex, "index-only"),
        ("malformed_name", mutate_malformed_name, "index-only"),
        ("name_ptr_oob", mutate_name_ptr_oob, "index-only"),
        ("unterminated_name", mutate_unterminated_string, "index-only"),
    ],
)
def test_mmb_mutation_parity(name, mut, category, tmp_path):
    mm0c = ensure_mm0c()
    mm0_path = ROOT / "examples" / "peano.mm0"
    mmb_path = ensure_peano_mmb()
    base = mmb_path.read_bytes()
    bad = tmp_path / f"{name}.mmb"
    bad.write_bytes(mut(base))

    with open(mm0_path, "rb") as mm0_file:
        ret = subprocess.run([mm0c, str(bad)], stdin=mm0_file).returncode

    data = bad.read_bytes()
    if ret == 0:
        load_mmb(data, strict_index=False, strict_align=False)
        if category == "index-only":
            with pytest.raises(Exception):
                load_mmb(data, strict_index=True, strict_align=False)
    else:
        with pytest.raises(Exception):
            load_mmb(data, strict_index=False, strict_align=False)
        with pytest.raises(Exception):
            load_mmb(data, strict_index=True, strict_align=False)


def test_truncated(tmp_path):
    mm0c = ensure_mm0c()
    mm0_path = ROOT / "examples" / "peano.mm0"
    mmb_path = ensure_peano_mmb()
    bad = tmp_path / "trunc.mmb"
    bad.write_bytes(mmb_path.read_bytes()[:100])
    with open(mm0_path, "rb") as mm0_file:
        with pytest.raises(subprocess.CalledProcessError):
            subprocess.run([mm0c, str(bad)], stdin=mm0_file, check=True)
    with pytest.raises(ValueError):
        load_mmb(bad.read_bytes(), strict_align=False)

