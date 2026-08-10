from pathlib import Path

from scripts.lean_min_imports import recommendations, rewrite_imports


def test_recommendations_use_final_missing_block() -> None:
    output = """warning: -- missing imports
import Mathlib.Old
warning: unneeded import 'Mathlib'
warning: -- missing imports
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.Basic
"""
    assert recommendations(output) == (
        {"Mathlib"},
        {"Mathlib.FieldTheory.Galois.Basic", "Mathlib.RingTheory.Valuation.Basic"},
    )


def test_rewrite_imports_preserves_body(tmp_path: Path) -> None:
    path = tmp_path / "Example.lean"
    source = "import Mathlib\nimport LastLib.Core\n\nnamespace Example\nend Example\n"
    path.write_text(source, encoding="utf-8")
    rewrite_imports(path, source, {"Mathlib"}, {"Mathlib.Algebra.Algebra.Basic"})
    assert path.read_text(encoding="utf-8") == (
        "import Mathlib.Algebra.Algebra.Basic\n"
        "import LastLib.Core\n\n"
        "namespace Example\nend Example\n"
    )
