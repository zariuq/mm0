import pathlib, sys, subprocess, shutil, pytest

# Ensure repository root on import path
ROOT = pathlib.Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import mmu


def run_mm0_hs(mm0_file, mmu_file, expect_fail=False):
    if shutil.which('mm0-hs') is None:
        return
    cmd = ["mm0-hs", "verify", mm0_file, mmu_file]
    if expect_fail:
        with pytest.raises(subprocess.CalledProcessError):
            subprocess.run(cmd, check=True)
    else:
        subprocess.run(cmd, check=True)


CASES = [
    ("examples/hello.mmu", False),
    ("examples/set11k.mmu", False),
    ("examples/peano.mmu", False),
    ("tests/mm0_mmu/good.mmu", False),
    ("tests/mm0_mmu/bad.mmu", True),
    ("tests/mm0_mmu/unknown.mmu", True),
    ("tests/mm0_mmu/bad_conv.mmu", True),
    ("tests/mm0_mmu/conv.mmu", False),
    ("tests/mm0_mmu/bad_unfold.mmu", True),
    ("tests/mm0_mmu/bad_refl.mmu", True),
]


@pytest.mark.parametrize("mmu_path, expect_fail", CASES)
def test_mmu_and_mm0_hs(mmu_path, expect_fail):
    if expect_fail:
        with pytest.raises(Exception):
            mmu.verify_mmu(mmu_path)
    else:
        mmu.verify_mmu(mmu_path)
    mm0_path = str(pathlib.Path(mmu_path).with_suffix('.mm0'))
    run_mm0_hs(mm0_path, mmu_path, expect_fail=expect_fail)

