import unittest
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent))
from translate_last_declaration import (
    AnthropicClient,
    build_prompt,
    collect_related_declaration_context,
    extract_declarations,
    extract_last_declaration,
    load_claude_settings,
    normalize_bare_latex_brackets,
    normalize_math_delimiters,
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

    def test_extracts_all_declarations(self):
        declarations = extract_declarations(
            "lemma helper (n : Nat) : n = n := by rfl\n"
            "theorem final : True := by exact True.intro\n"
        )
        self.assertEqual([item.name for item in declarations], ["helper", "final"])
        self.assertEqual(declarations[0].statement, "lemma helper (n : Nat) : n = n")
        self.assertEqual(declarations[1].proof, "by exact True.intro")

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

    def test_prompt_requires_semantic_references_and_math_environments(self):
        declaration = extract_last_declaration("theorem final (n : Nat) : n = n := by rfl\n")
        assert declaration is not None
        prompt = build_prompt(declaration, "Paper/items/thm_1.lean")
        self.assertRegex(prompt, r"concrete mathematical\s+content")
        self.assertIn("Never stop at a", prompt)
        self.assertIn("Use `$...$` for short inline mathematics", prompt)
        self.assertIn("Never use `\\(...\\)` or `\\[...\\]`", prompt)
        self.assertIn("Never use bare square brackets as math delimiters", prompt)
        self.assertIn(r"\operatorname{deriv}", prompt)
        self.assertIn("provided only as reference context", prompt)

    def test_collects_cited_result_from_local_import_graph(self):
        import tempfile

        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            helper_path = project / "TheoremLib/Paper/helper.lean"
            main_path = project / "TheoremLib/Paper/main.lean"
            helper_path.parent.mkdir(parents=True)
            helper_path.write_text(
                "theorem energy_decreases (E : Real → Real) : True := by trivial\n",
                encoding="utf-8",
            )
            main_path.write_text(
                "import TheoremLib.Paper.helper\n"
                "theorem final (E : Real → Real) : True := by\n"
                "  exact energy_decreases E\n",
                encoding="utf-8",
            )
            declaration = extract_last_declaration(main_path.read_text(encoding="utf-8"))
            assert declaration is not None
            context = collect_related_declaration_context(declaration, main_path, project)
            self.assertIn("TheoremLib/Paper/helper.lean", context)
            self.assertIn("theorem energy_decreases (E : Real → Real) : True", context)
            self.assertNotIn("by trivial", context)

    def test_resolves_shortened_theoremlib_import_alias(self):
        import tempfile

        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            helper_path = project / "TheoremLib/Abbas_Dynamical_systems_2015/items/lem_5.lean"
            main_path = project / "TheoremLib/Abbas_Dynamical_systems_2015/items/prop_1.lean"
            helper_path.parent.mkdir(parents=True)
            helper_path.write_text(
                "theorem subgradient_chain_rule (x : Real) : True := by trivial\n",
                encoding="utf-8",
            )
            main_path.write_text(
                "import TheoremLib.Abbas_Dynamical_systems_associated_with_the_sum_2015.items.lem_5\n"
                "theorem final (x : Real) : True := by\n"
                "  exact subgradient_chain_rule x\n",
                encoding="utf-8",
            )
            declaration = extract_last_declaration(main_path.read_text(encoding="utf-8"))
            assert declaration is not None
            context = collect_related_declaration_context(declaration, main_path, project)
            self.assertIn("subgradient_chain_rule (x : Real) : True", context)

    def test_related_context_ignores_uncited_results(self):
        import tempfile

        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            main_path = project / "TheoremLib/Paper/main.lean"
            main_path.parent.mkdir(parents=True)
            main_path.write_text(
                "lemma used_result : True := by trivial\n"
                "lemma unused_result : True := by trivial\n"
                "theorem final : True := by exact used_result\n",
                encoding="utf-8",
            )
            declaration = extract_last_declaration(main_path.read_text(encoding="utf-8"))
            assert declaration is not None
            context = collect_related_declaration_context(declaration, main_path, project)
            self.assertIn("lemma used_result : True", context)
            self.assertNotIn("unused_result", context)

    def test_normalizes_bare_latex_brackets_with_nested_interval(self):
        text = (
            r"the function [ t\mapsto (\Phi(x(t)))_{\mathbb R} ] is absolutely continuous "
            r"on [0,T], and [ \operatorname{deriv}(t\mapsto \Phi(x(t)))(t) "
            r"=\langle v(t),\operatorname{deriv}x(t)\rangle \text{ on } [0,T] ]."
        )
        normalized = normalize_bare_latex_brackets(text)
        self.assertIn(r"the function \(t\mapsto (\Phi(x(t)))_{\mathbb R}\)", normalized)
        self.assertIn(r"\(\operatorname{deriv}", normalized)
        self.assertIn(r"\text{ on } [0,T]\)", normalized)
        self.assertIn("on [0,T]", normalized)

    def test_normalizer_preserves_code_fences_and_markdown_links(self):
        text = "`[ t\\mapsto f(t) ]` and [label \\mapsto value](target)\n```lean\n[ t\\mapsto f(t) ]\n```"
        self.assertEqual(normalize_bare_latex_brackets(text), text)

    def test_normalizer_preserves_already_delimited_math(self):
        text = r"Already valid \( [\operatorname{dom} f] \) and \[ [0,T] \]."
        self.assertEqual(normalize_bare_latex_brackets(text), text)

    def test_normalizes_standalone_bare_display_delimiters(self):
        text = "The conclusion is\n[\n\\operatorname{deriv} f(t) = 0\n]\nfor almost every t."
        expected = "The conclusion is\n\\[\n\\operatorname{deriv} f(t) = 0\n\\]\nfor almost every t."
        self.assertEqual(normalize_bare_latex_brackets(text), expected)

    def test_normalizes_legacy_math_delimiters_to_github_dialect(self):
        text = "A bound \\(0<L\\) holds:\n\\[\nf(x)\\le L\n\\]\nand that is all."
        expected = "A bound $0<L$ holds:\n\n$$\nf(x)\\le L\n$$\n\nand that is all."
        self.assertEqual(normalize_math_delimiters(text), expected)

    def test_normalizer_pads_inline_math_that_follows_a_word_character(self):
        self.assertEqual(normalize_math_delimiters(r"the step-\(r\) map"), "the step- $r$ map")

    def test_normalizer_merges_formulas_glued_by_a_hyphen(self):
        self.assertEqual(
            normalize_math_delimiters(r"an \(\varepsilon\)-\(T\) statement"),
            r"an $\varepsilon\text{-}T$ statement",
        )

    def test_normalizer_keeps_code_fences_and_break_commands(self):
        text = "```lean\n\\(x\\)\n```\n\n$$\na+\\\\[4pt]b\n$$\n"
        self.assertEqual(normalize_math_delimiters(text), "```lean\n\\(x\\)\n```\n\n$$\na+\\\\[4pt]b\n$$\n")

    def test_normalizer_is_idempotent(self):
        once = normalize_math_delimiters("inline \\(x\\) then\n\\[\ny\n\\]\ndone")
        self.assertEqual(normalize_math_delimiters(once), once)

    def test_render_markdown_emits_only_github_math_delimiters(self):
        declaration = extract_last_declaration("theorem final (n : Nat) : n = n := by rfl\n")
        assert declaration is not None
        response = "The value \\(n\\) satisfies\n\\[\nn=n\n\\]\nand the proof is `rfl`.\n===PROOF_EXPLANATION===\nUse \\(rfl\\)."
        rendered = render_markdown(declaration, "Paper/items/thm_1.lean", response)
        self.assertNotIn("\\(", rendered)
        self.assertNotIn("\\[", rendered)
        self.assertIn("The value $n$ satisfies", rendered)
        self.assertIn("$$\nn=n\n$$", rendered)
        self.assertIn("Use $rfl$.", rendered)

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
