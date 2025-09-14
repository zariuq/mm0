import pathlib
import subprocess
import shutil
import pytest

ROOT = pathlib.Path(__file__).resolve().parent.parent


def ensure_mm0c() -> str:
    mm0c = shutil.which('mm0-c')
    if mm0c:
        return mm0c
    mm0c_path = ROOT / 'mm0-c' / 'mm0-c'
    if mm0c_path.exists():
        return str(mm0c_path)
    gcc = shutil.which('gcc')
    if gcc is None:
        pytest.skip('gcc not available to build mm0-c')
    subprocess.run([gcc, str(ROOT / 'mm0-c' / 'main.c'), '-O2', '-o', str(mm0c_path)], check=True)
    return str(mm0c_path)


def test_mmb_verify():
    mm0c = ensure_mm0c()
    mm0_path = ROOT / 'examples' / 'peano.mm0'
    mmb_path = ROOT / 'examples' / 'peano.mmb'
    if not mmb_path.exists():
        pytest.skip('peano.mmb not found')
    with open(mm0_path, 'rb') as mm0_file:
        subprocess.run([mm0c, str(mmb_path)], stdin=mm0_file, check=True)
    subprocess.run(['python3', str(ROOT / 'mmu.py'), str(mm0_path), str(mmb_path)], check=True)


def test_mmb_invalid():
    mm0c = ensure_mm0c()
    bad_mmb = ROOT / 'tests' / 'mmb' / 'run' / 'gi_header_p_index_overflow.mmb'
    with pytest.raises(subprocess.CalledProcessError):
        subprocess.run([mm0c, str(bad_mmb)], stdin=subprocess.DEVNULL, check=True)
    with pytest.raises(subprocess.CalledProcessError):
        subprocess.run(
            ['python3', str(ROOT / 'mmu.py'), str(ROOT / 'examples' / 'peano.mm0'), str(bad_mmb)],
            check=True,
        )
