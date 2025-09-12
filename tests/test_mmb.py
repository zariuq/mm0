import pathlib, subprocess, shutil, pytest

ROOT = pathlib.Path(__file__).resolve().parent.parent


def ensure_mm0c():
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


def compile_peano_mmb(tmp_path):
    if shutil.which('mm0-rs') is None:
        pytest.skip('mm0-rs not available')
    mmb_path = tmp_path / 'peano.mmb'
    subprocess.run(['mm0-rs', 'compile', str(ROOT / 'examples' / 'peano.mm1'), str(mmb_path)], check=True)
    return mmb_path


def test_mmb_verify(tmp_path):
    mm0c = ensure_mm0c()
    mmb_path = compile_peano_mmb(tmp_path)
    with open(ROOT / 'examples' / 'peano.mm0', 'rb') as mm0_file:
        subprocess.run([mm0c, str(mmb_path)], stdin=mm0_file, check=True)


def test_mmb_invalid():
    mm0c = ensure_mm0c()
    with pytest.raises(subprocess.CalledProcessError):
        subprocess.run(
            [mm0c, str(ROOT / 'tests' / 'mmb' / 'run' / 'gi_header_p_index_overflow.mmb')],
            stdin=subprocess.DEVNULL,
            check=True,
        )
