import unittest
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent))
from translate_last_declaration import (
    AnthropicClient,
    extract_last_declaration,
    load_claude_settings,
    output_path_for,
    render_markdown,
    split_explanations,
)


class ExtractLastDeclarationTests(unittest.TestCase):
    def test_last_theorem_and_proof(self):
        source = """import Mathlib
namespace Demo
def helper : Nat := 1
private theorem first : True := by trivial
theorem final (n : Nat) : n = n := by rfl
end Demo
"""
        declaration = extract_last_declaration(source)
        self.assertIsNotNone(declaration)
        assert declaration is not None
        self.assertEqual(declaration.kind, "theorem")
        self.assertEqual(declaration.name, "final")
        self.assertIn("(n : Nat)", declaration.statement)
        self.assertEqual(declaration.proof, "by rfl")
        self.assertNotIn("end Demo", declaration.source)

    def test_last_declaration_without_proof(self):
        declaration = extract_last_declaration("def x : Nat := 1\n")
        self.assertIsNotNone(declaration)
        assert declaration is not None
        self.assertEqual(declaration.kind, "def")
        self.assertIsNone(declaration.proof)

    def test_comments_do_not_create_declarations(self):
        source = """/- theorem fake : False := by contradiction -/
theorem real : True := by trivial
"""
        declaration = extract_last_declaration(source)
        self.assertIsNotNone(declaration)
        assert declaration is not None
        self.assertEqual(declaration.name, "real")

    def test_recall_is_a_declaration(self):
        declaration = extract_last_declaration("namespace Demo\nrecall opial_lemma\nend Demo\n")
        self.assertIsNotNone(declaration)
        assert declaration is not None
        self.assertEqual(declaration.kind, "recall")
        self.assertEqual(declaration.name, "opial_lemma")
        self.assertIsNone(declaration.proof)

    def test_output_mapping(self):
        root = Path("/tmp/TheoremLib")
        output = Path("/tmp/NL")
        path = root / "Paper" / "items" / "thm_1.lean"
        self.assertEqual(output_path_for(path, root, output), output / "Paper/items/thm_1.md")

    def test_claude_code_auth_token_is_supported(self):
        import os

        previous = {key: os.environ.get(key) for key in ("ANTHROPIC_AUTH_TOKEN", "ANTHROPIC_API_KEY", "DEEPSEEK_API_KEY")}
        try:
            os.environ["ANTHROPIC_AUTH_TOKEN"] = "auth-token"
            os.environ.pop("ANTHROPIC_API_KEY", None)
            os.environ.pop("DEEPSEEK_API_KEY", None)
            self.assertEqual(
                os.getenv("ANTHROPIC_AUTH_TOKEN", os.getenv("ANTHROPIC_API_KEY", os.getenv("DEEPSEEK_API_KEY", ""))),
                "auth-token",
            )
        finally:
            for key, value in previous.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value

    def test_load_claude_settings_reads_env_and_preserves_process_environment(self):
        import os
        import tempfile

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "settings.json"
            path.write_text(
                '{"env": {"TEST_OPT_PAPER_SETTINGS_KEY": "from-settings", '
                '"TEST_OPT_PAPER_EXISTING_KEY": "settings-value"}, '
                '"permissions": {"allow": []}}',
                encoding="utf-8",
            )
            os.environ.pop("TEST_OPT_PAPER_SETTINGS_KEY", None)
            os.environ["TEST_OPT_PAPER_EXISTING_KEY"] = "from-process"
            try:
                load_claude_settings(path)
                self.assertEqual(os.environ["TEST_OPT_PAPER_SETTINGS_KEY"], "from-settings")
                self.assertEqual(os.environ["TEST_OPT_PAPER_EXISTING_KEY"], "from-process")
            finally:
                os.environ.pop("TEST_OPT_PAPER_SETTINGS_KEY", None)
                os.environ.pop("TEST_OPT_PAPER_EXISTING_KEY", None)

    def test_markdown_order_and_english_layout(self):
        declaration = extract_last_declaration("theorem final (n : Nat) : n = n := by rfl\n")
        assert declaration is not None
        rendered = render_markdown(declaration, "Paper/items/thm_1.lean", "It is reflexive.\n===PROOF_EXPLANATION===\nThe proof uses rfl.")
        order = [
            "## Source file",
            "## Lean statement",
            "## Statement explanation",
            "## Lean proof",
            "## Proof explanation",
        ]
        self.assertEqual([rendered.index(item) for item in order], sorted(rendered.index(item) for item in order))
        self.assertIn("It is reflexive.", rendered)
        self.assertIn("The proof uses rfl.", rendered)

    def test_split_explanations_without_separator(self):
        statement, proof = split_explanations("Only one explanation")
        self.assertEqual(statement, "Only one explanation")
        self.assertIn("No proof explanation", proof)
    def test_anthropic_request_uses_documented_defaults(self):
        client = AnthropicClient("key", "https://api.deepseek.com/anthropic", "deepseek-v4-pro", 1, 0)
        self.assertEqual(client.model, "deepseek-v4-pro")
        self.assertTrue(client.endpoint.endswith("/anthropic/v1/messages"))

    def test_anthropic_request_shape_and_response(self):
        from unittest.mock import patch

        class Response:
            def __enter__(self):
                return self

            def __exit__(self, *args):
                return False

            def read(self):
                return json.dumps({"content": [{"type": "text", "text": "translated"}]}).encode()

        client = AnthropicClient("secret", "https://api.deepseek.com/anthropic", "deepseek-v4-pro", 1, 0)
        with patch("translate_last_declaration.urllib.request.urlopen", return_value=Response()) as mocked:
            self.assertEqual(client.translate("hello"), "translated")
        request = mocked.call_args.args[0]
        self.assertEqual(request.full_url, "https://api.deepseek.com/anthropic/v1/messages")
        self.assertEqual(request.get_header("X-api-key"), "secret")
        payload = json.loads(request.data)
        self.assertEqual(payload["max_tokens"], 32768)
        self.assertEqual(payload["messages"][0]["content"][0]["type"], "text")
        self.assertFalse(payload["stream"])


if __name__ == "__main__":
    unittest.main()
