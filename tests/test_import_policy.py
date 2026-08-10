from pathlib import Path

from scripts.check_lean_import_policy import violations


def test_import_policy_rejects_mathlib_umbrella(tmp_path: Path) -> None:
    path = tmp_path / "lean" / "LastLib" / "Book02Example" / "Chapter01" / "Section01.lean"
    path.parent.mkdir(parents=True)
    path.write_text("import Mathlib\n", encoding="utf-8")
    assert "forbidden umbrella import `Mathlib`" in violations(path)[0]


def test_import_policy_rejects_chapter_aggregator_from_leaf(tmp_path: Path) -> None:
    path = tmp_path / "lean" / "LastLib" / "Book02Example" / "Chapter01" / "Section01.lean"
    path.parent.mkdir(parents=True)
    path.write_text(
        "import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12\n", encoding="utf-8"
    )
    assert "leaf module imports aggregator" in violations(path)[0]


def test_import_policy_allows_focused_modules(tmp_path: Path) -> None:
    path = tmp_path / "lean" / "LastLib" / "Book02Example" / "Chapter01" / "Section01.lean"
    path.parent.mkdir(parents=True)
    path.write_text(
        "import Mathlib.FieldTheory.RamificationInertia\n"
        "import LastLib.Book01Example.Chapter12.Core\n",
        encoding="utf-8",
    )
    assert violations(path) == []
