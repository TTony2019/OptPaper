import tempfile
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent))
from update_readme import is_open_item


class OpenItemTests(unittest.TestCase):
    def assert_open(self, source: str, expected: bool) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "item.lean"
            path.write_text(source, encoding="utf-8")
            self.assertEqual(is_open_item(path), expected)

    def test_sorry_and_admit_are_open(self):
        self.assert_open("theorem unfinished : True := by sorry\n", True)
        self.assert_open("theorem unfinished : True := by admit\n", True)

    def test_axiom_and_constant_declarations_are_open(self):
        self.assert_open("axiom unfinished : True\n", True)
        self.assert_open("private constant unfinished : Nat\n", True)

    def test_comments_and_strings_are_ignored(self):
        self.assert_open(
            """/- sorry admit axiom constant -/
-- sorry
def note : String := "sorry admit axiom constant"
theorem finished : True := by trivial
""",
            False,
        )

    def test_constant_constructors_are_not_open(self):
        self.assert_open(
            """inductive Run where
  | constant

def value : Run -> Nat
  | .constant => 1
""",
            False,
        )


if __name__ == "__main__":
    unittest.main()
