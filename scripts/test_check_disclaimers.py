"""Unit tests for scripts/check_disclaimers.py, on synthetic Lean modules."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_disclaimers as c  # noqa: E402

HEADER = "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n\npublic section\n\n"
CANARY_NAME = "Cslib.Crypto.Canary.cpaSecure"
CANARY_SENTENCE = ("The caller supplies `hB`, the bound on the advantage of the reduction "
                   "`toDDH A`, and no efficiency certificate for `toDDH` is proved.")


def canary(tracking: str = "") -> str:
    """The canary module. Its theorem is named for CPA security, but its hypothesis `hB` assumes
    the hard part of its conclusion, that the constructed reduction has negligible advantage, and
    its docstring says so honestly. `tracking` is appended to the docstring."""
    return (HEADER + "namespace Cslib.Crypto.Canary\n\n"
            "/-- **The scheme is CPA secure.** The caller supplies `hB`, the bound on the\n"
            "advantage of the reduction `toDDH A`, and no efficiency certificate for `toDDH` is\n"
            f"proved.{tracking} -/\n"
            "theorem cpaSecure (A : Adversary)\n"
            "    (hB : Negligible fun n => ddhAdvantage (toDDH A) n) :\n"
            "    Negligible fun n => cpaAdvantage A n := by\n"
            "  simpa [cpaAdvantage_eq] using hB\n\n"
            "end Cslib.Crypto.Canary\n")


PATH = "CslibFrontier/Crypto/A.lean"
OTHER_PATH = "CslibFrontier/Crypto/B.lean"


def hits(source: str, records: dict[str, str] | None = None) -> list[tuple[str, str, str]]:
    """The disclaimers of the module `PATH` with the text `source` as `(declaration, sentence,
    tracked)`, given the recorded declarations `records` with their modules."""
    return [(hit.declaration, hit.sentence, hit.tracked)
            for hit in c.module_hits(PATH, source, records or {})]


def found(doc: str) -> list[str]:
    """The disclaimers of a module docstring with the body `doc`."""
    return [sentence for _, sentence, _ in hits(f"/-! {doc} -/\n")]


def named(name: str) -> str:
    return f"the entry of {name}"


class RuleTests(unittest.TestCase):
    def test_canary_an_honest_disclaimer_without_an_issue_is_untracked(self) -> None:
        self.assertEqual(hits(canary()), [(CANARY_NAME, CANARY_SENTENCE, "")])
        hit, = c.module_hits(PATH, canary(), {})
        self.assertEqual(hit.line, 10)

    def test_an_issue_number_in_the_docstring_tracks_it(self) -> None:
        self.assertEqual(hits(canary(" Tracked in #5293.")),
                         [(CANARY_NAME, CANARY_SENTENCE, "#5293")])
        link = " See [#612](https://github.com/cslib-community/cslib-frontier/issues/612)."
        self.assertEqual(hits(canary(link))[0][2], "#612")
        # Too short, too long, or not a number of its own.
        for other in (" See #12.", " See #123456.", " See rule#5293.", " See issue 5293."):
            with self.subTest(other=other):
                self.assertEqual(hits(canary(other))[0][2], "")
        # A number in another docstring does not track this one.
        other = "\n/-- Tracked in #5293. -/\ntheorem u : True := trivial\n"
        self.assertEqual(hits(canary() + other), [(CANARY_NAME, CANARY_SENTENCE, "")])

    def test_a_baseline_entry_of_the_declaration_tracks_it(self) -> None:
        self.assertEqual(hits(canary(), {CANARY_NAME: PATH}),
                         [(CANARY_NAME, CANARY_SENTENCE, c.OWN)])
        self.assertEqual(hits(canary(), {"Cslib.Crypto.Canary.other": PATH, "cpaSecure": PATH}),
                         [(CANARY_NAME, CANARY_SENTENCE, "")])
        # An issue number is reported first, and the declaration's own entry before a named one.
        both = {CANARY_NAME: PATH, "Cslib.Crypto.Canary.toDDH": PATH}
        self.assertEqual(hits(canary(" Tracked in #5293."), both)[0][2], "#5293")
        self.assertEqual(hits(canary(), both)[0][2], c.OWN)

    def test_an_unrelated_entry_of_the_module_does_not_track_a_module_docstring(self) -> None:
        source = "/-! # Title\n\nRunning time is not tracked. -/\n" + canary()
        sentence = "Running time is not tracked."
        self.assertEqual(hits(source)[0], (c.MODULE_DOC, sentence, ""))
        # Neither the entry of a declaration of the module, nor that of the canary itself.
        self.assertEqual(hits(source, {"Cslib.Crypto.Canary.other": PATH})[0],
                         (c.MODULE_DOC, sentence, ""))
        self.assertEqual([t for _, _, t in hits(source, {CANARY_NAME: PATH})], ["", c.OWN])
        # An issue number in the module docstring does, and only there.
        cited = source.replace("is not tracked.", "is not tracked (#5293).")
        self.assertEqual([t for _, _, t in hits(cited)], ["#5293", ""])

    def test_a_sentence_that_names_a_recorded_declaration_is_tracked(self) -> None:
        to_ddh = "Cslib.Crypto.Canary.toDDH"
        # The canary names its reduction: `toDDH A` and `toDDH`.
        self.assertEqual(hits(canary(), {to_ddh: PATH}),
                         [(CANARY_NAME, CANARY_SENTENCE, named(to_ddh))])
        # In a module docstring, by the full name or by the name an entry of the module ends with.
        for written in (to_ddh, "toDDH", "Canary.toDDH", "_root_." + to_ddh):
            with self.subTest(written=written):
                source = f"/-! `{written}` has no efficiency certificate. -/\n" + canary(" #5293")
                self.assertEqual(hits(source, {to_ddh: PATH})[0][2], named(to_ddh))
        # Another sentence of the same docstring is not tracked by the name.
        source = "/-! Depth is not certified. The reduction `toDDH` has no PPT certificate. -/\n"
        self.assertEqual([t for _, _, t in hits(source, {to_ddh: PATH})], ["", named(to_ddh)])
        # The name must be in a code span and must be the whole identifier.
        for doc in ("toDDH has no efficiency certificate.", "`toDDH'` is not certified.",
                    "`A.toDDH` is not certified.", "`toDDH.spec` is not certified.",
                    "`DDH` is not certified."):
            with self.subTest(doc=doc):
                self.assertEqual(hits(f"/-! {doc} -/\n", {to_ddh: PATH})[0][2], "")

    def test_a_written_name_resolves_through_namespaces_or_within_the_module(self) -> None:
        def tracked(doc: str, records: dict[str, str], namespace: str = "A.B") -> str:
            source = (f"namespace {namespace}\n/-- {doc} -/\ntheorem C.t : True := trivial\n"
                      f"end {namespace}\n")
            return hits(HEADER + source, records)[0][2]
        doc = "`reduction` has no efficiency certificate."
        # As Lean reads it: the declaration's namespace first, then the enclosing ones.
        records = {"A.B.C.reduction": OTHER_PATH, "A.B.reduction": OTHER_PATH,
                   "A.reduction": OTHER_PATH, "reduction": OTHER_PATH, "X.reduction": PATH}
        self.assertEqual(tracked(doc, records), named("A.B.C.reduction"))
        del records["A.B.C.reduction"]
        self.assertEqual(tracked(doc, records), named("A.B.reduction"))
        self.assertEqual(tracked(doc, records, "A"), named("A.reduction"))
        self.assertEqual(tracked(doc, records, "Z"), named("reduction"))
        # Otherwise the one entry of this module that ends with the name.
        self.assertEqual(tracked(doc, {"X.reduction": PATH}), named("X.reduction"))
        self.assertEqual(tracked("`X.reduction` is not certified.", {"W.X.reduction": PATH}),
                         named("W.X.reduction"))
        # Two such entries are ambiguous, and an entry of another module is not looked at.
        self.assertEqual(tracked(doc, {"X.reduction": PATH, "Y.reduction": PATH}), "")
        self.assertEqual(tracked(doc, {"X.reduction": OTHER_PATH}), "")
        self.assertEqual(tracked(doc, {"X.reduction": PATH, "Y.reduction": OTHER_PATH}),
                         named("X.reduction"))
        self.assertEqual(tracked(doc, {"X.thereduction": PATH}), "")
        # A module docstring is read outside every namespace.
        source = "namespace A\n/-! `reduction` has no efficiency certificate. -/\nend A\n"
        self.assertEqual(hits(source, {"A.reduction": OTHER_PATH})[0][2], "")
        self.assertEqual(hits(source, {"A.reduction": PATH})[0][2], named("A.reduction"))

    def test_comments_strings_and_code_are_not_read(self) -> None:
        self.assertEqual(hits(
            HEADER + "-- This does not prove security: the caller supplies the reduction.\n"
            "/- This block does not prove security, and has no efficiency certificate. -/\n"
            "def note : String := \"the caller supplies it; no efficiency certificate\"\n"
            "def raw : String := r#\"this is not proved here\"#\n"
            "/-- A plain fact. -/\n"
            "theorem t (limitations : Nat) : True := by\n"
            "  -- running time is not tracked\n"
            "  trivial\n"), [])
        # A docstring inside a string or a comment is not a docstring.
        self.assertEqual(hits("def s : String := \"/-- this is not proved here -/\"\n"
                              "-- /-- this is not proved here -/\n"), [])

    def test_attachment_follows_namespaces_and_fields(self) -> None:
        doc = "/-- Depth is not certified. -/\n"
        def name(source: str) -> str:
            return hits(HEADER + source)[0][0]
        self.assertEqual(name(doc + "theorem t : True := trivial\n"), "t")
        self.assertEqual(name("namespace A.B\nnamespace C\n" + doc + "@[simp]\nprivate lemma t' "
                              ": True := trivial\nend C\nend A.B\n"), "A.B.C.t'")
        self.assertEqual(name("namespace A\nend A\n" + doc + "def f := 1\n"), "f")
        self.assertEqual(name("namespace A\n" + doc + "theorem _root_.B.t : True := trivial\n"),
                         "B.t")
        self.assertEqual(name("namespace A\nstructure S where\n  " + doc + "  field : Nat\n"
                              "  other : Nat\nend A\n"), "A.S")
        self.assertEqual(name("inductive T where\n  " + doc + "  | mk : T\n"), "T")

    def test_attachment_is_approximate(self) -> None:
        doc = "/-- Depth is not certified. -/\n"
        for source in (doc + "instance : Inhabited Nat := ⟨0⟩\n",
                       doc + "macro \"foo\" : term => `(1)\n",
                       doc + "notation \"𝔽\" => Foo\n",
                       doc + "alias a := b\n"):
            with self.subTest(source=source):
                self.assertEqual(hits(HEADER + source), [("", "Depth is not certified.", "")])

    def test_each_pattern_matches(self) -> None:
        examples = (
            "This does not prove the book's conclusion.", "They do not yet establish security.",
            "The record does not certify key generation.", "It does not claim security.",
            "The keyed bound is not proved.", "The remaining parts are not established here.",
            "Depth is not yet certified.", "Theorem 6.9, the PRF, was not proved here.",
            "It has no efficiency certificate.", "No strict-PPT certificate is proved for it.",
            "It carries no PPT witness.", "This assumes the reduction is efficient.",
            "Assuming that the reduction is PPT, the scheme is secure.",
            "The caller supplies the pad test.", "The caller provides the bound.",
            "The efficiency of `B` is left to the caller.", "Circular security is not asserted.",
            "`SecureKDF` is assumed as a hypothesis.", "The decoder is taken as a hypothesis.",
            "The learner contract remains a hypothesis.", "The textbook definition remains open.",
            "General word-level games remain open.", "## Limitations", "A limitation of the model.",
            "Running time is not tracked.", "An algebraic helper, not a security theorem.",
            "Perfect privacy of the idealized stand-in.")
        for example in examples:
            with self.subTest(example=example):
                self.assertEqual(found(example), [example])
                self.assertEqual(found(example.upper()), [example.upper()])
        self.assertEqual({p for p in c.PATTERNS
                          if not any(c.re.search(p, e, c.re.I) for e in examples)}, set())

    def test_near_misses_do_not_match(self) -> None:
        for example in ("This proves the theorem.", "The challenge is supplied by the caller.",
                        "This module does not claim agreement with a future revision.",
                        "The delimitation of the blocks is fixed.", "Games without stand-ins.",
                        "The proof is established here.", "`h_is not proved` is a name.",
                        "See `batchSPIR_limitation`.", "The caller's input is a word."):
            with self.subTest(example=example):
                self.assertEqual(found(example), [])

    def test_a_docstring_is_cut_into_sentences(self) -> None:
        def cut(doc: str) -> list[str]:
            return [text for _, text in c.sentences(doc)]
        self.assertEqual(cut("First.  Second, e.g. `x`\nand (p. 3) more. `Third` one! Is it? Yes."),
                         ["First.", "Second, e.g. `x` and (p. 3) more.", "`Third` one!", "Is it?",
                          "Yes."])
        self.assertEqual(cut("**Title.** Body of 2.5 parts (see Thm. 4). End."),
                         ["**Title.**", "Body of 2.5 parts (see Thm. 4).", "End."])
        self.assertEqual(cut("Intro:\n* one item\n  continued\n- another\n1. numbered\n\n"
                             "## What is not proved\n\nA paragraph\nof two lines"),
                         ["Intro:", "one item continued", "another", "numbered",
                          "## What is not proved", "A paragraph of two lines"])
        # Only the sentence with the phrase is the disclaimer, and a phrase may span a line break.
        self.assertEqual(found("A fact. The bound is not\n  proved here. Another fact."),
                         ["The bound is not proved here."])
        self.assertEqual(found("## What is not proved\n\n* Privacy of the client."),
                         ["## What is not proved"])

    def test_the_digest_ignores_wrapping_and_case_only(self) -> None:
        self.assertEqual(c.digest("The bound is  not\nproved here."),
                         c.digest("the bound is not proved here."))
        self.assertNotEqual(c.digest("The bound is not proved here."),
                            c.digest("The keyed bound is not proved here."))
        self.assertRegex(c.digest("x"), r"^[0-9a-f]{12}$")


class RatchetTests(unittest.TestCase):
    A, B = "CslibFrontier/Crypto/A.lean", "CslibFrontier/Crypto/B.lean"
    OLD = "The keyed bound is not proved here."

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write(self.A, self.module(self.OLD))
        self.write(self.B, self.module("A plain fact."))
        self.write("CslibFrontier/Logic/C.lean", self.module("Outside the roots: not proved here."))
        self.write(c.BASELINE, c.baseline_text(c.update(c.scan(self.root), {}, None)))
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    @staticmethod
    def module(*docs: str) -> str:
        return HEADER + "".join(f"/-- {doc} -/\ntheorem t{i} : True := trivial\n\n"
                                for i, doc in enumerate(docs))

    def git(self, *args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def run_main(self, *args: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main([*args, "--root", str(self.root)])
        return code, out.getvalue(), err.getvalue()

    def baseline(self) -> dict[str, dict]:
        return json.loads((self.root / c.BASELINE).read_text(encoding="utf-8"))

    def test_the_initial_baseline_records_the_untracked_disclaimers_of_the_roots(self) -> None:
        self.assertEqual(self.baseline(),
                         {f"{self.A}:{c.digest(self.OLD)}": {"sentence": self.OLD}})
        for args in ((), ("--enforce",), ("--all", "--enforce"), ("--report",)):
            code, out, err = self.run_main(*args)
            self.assertEqual((code, err), (0, ""))
            self.assertIn("1 disclaimer(s) under CslibFrontier/Crypto: 0 tracked (0 by an issue "
                          "number, 0 by their declaration's baseline entry, 0 by the entry of a "
                          "declaration they name), 1 untracked, of which 1 baselined and 0 new; "
                          "0 stale baseline entries", out)

    def test_canary_a_new_untracked_disclaimer_fails_only_when_enforced(self) -> None:
        self.write("CslibFrontier/Crypto/Canary.lean", canary())
        code, out, err = self.run_main()
        self.assertEqual((code, err), (0, ""))
        self.assertIn(f"CslibFrontier/Crypto/Canary.lean:10: {CANARY_NAME}\n    {CANARY_SENTENCE}",
                      out)
        self.assertIn("1 baselined and 1 new", out)
        self.assertIn("report only: enforcement is not switched on yet", out)
        code, out, err = self.run_main("--enforce")
        self.assertEqual(code, 1)
        self.assertIn(f"CslibFrontier/Crypto/Canary.lean:10: {CANARY_NAME}", err)
        self.assertIn("A stated limitation is tracked", err)
        self.assertEqual(self.run_main("--all", "--enforce")[0], 1)
        code, out, _ = self.run_main("--report")
        self.assertEqual(code, 0)
        self.assertIn(CANARY_SENTENCE, out)

    def test_a_tracked_disclaimer_passes(self) -> None:
        canary_path = "CslibFrontier/Crypto/Canary.lean"
        self.write(canary_path, canary(" Tracked in #5293."))
        code, out, _ = self.run_main("--enforce")
        self.assertEqual(code, 0)
        self.assertIn("2 disclaimer(s) under CslibFrontier/Crypto: 1 tracked (1 by an issue "
                      "number, 0 by their declaration's baseline entry, 0 by the entry of a "
                      "declaration they name), 1 untracked", out)
        # Through the security-premise entry of the canary theorem itself.
        self.write(canary_path, canary())
        self.write(c.RECORDS[0], json.dumps({CANARY_NAME: {
            "module": canary_path, "premises": ["hB"], "why": "helper"}}))
        code, out, _ = self.run_main("--enforce")
        self.assertEqual(code, 0)
        self.assertIn("1 tracked (0 by an issue number, 1 by their declaration's baseline entry, "
                      "0 by the entry of a declaration they name)", out)
        # Through the reduction-witness entry of the reduction that the sentence names.
        self.write(c.RECORDS[0], "{}")
        self.assertEqual(self.run_main("--enforce")[0], 1)
        self.write(c.RECORDS[1], json.dumps({"Cslib.Crypto.Canary.toDDH": {
            "module": canary_path, "kind": "gap", "why": "tracked in #5293"}}))
        code, out, _ = self.run_main("--enforce")
        self.assertEqual(code, 0)
        self.assertIn("1 tracked (0 by an issue number, 0 by their declaration's baseline entry, "
                      "1 by the entry of a declaration they name)", out)
        code, out, _ = self.run_main("--list")
        self.assertIn(f"{canary_path}:10: {CANARY_NAME}: tracked by the entry of "
                      "Cslib.Crypto.Canary.toDDH", out)

    def test_an_unrelated_entry_of_the_module_does_not_track_its_module_docstring(self) -> None:
        self.write(self.B, "/-! Running time is not tracked. -/\n" + self.module("A plain fact."))
        self.write(c.RECORDS[1], json.dumps({"Cslib.Crypto.red": {
            "module": self.B, "kind": "gap", "why": "tracked in #5293"}}))
        code, _, err = self.run_main("--enforce")
        self.assertEqual(code, 1)
        self.assertIn(f"{self.B}:1: {c.MODULE_DOC}\n    Running time is not tracked.", err)
        self.write(self.B, "/-! Running time of `red` is not tracked. -/\n"
                   + self.module("A plain fact."))
        self.assertEqual(self.run_main("--enforce")[0], 0)

    def test_moving_and_rewrapping_a_sentence_keeps_its_entry(self) -> None:
        self.write(self.A, self.module("A new first theorem.", "Some context. The keyed bound\n"
                                       "  is NOT proved here. More context."))
        self.assertEqual(self.run_main("--enforce")[0], 0)

    def test_a_reworded_sentence_is_new_and_its_entry_stale(self) -> None:
        self.write(self.A, self.module("The keyed bound (5.22) is not proved here."))
        code, _, err = self.run_main("--enforce")
        self.assertEqual(code, 1)
        self.assertIn(f"{self.A}:8: t0\n    The keyed bound (5.22) is not proved here.", err)
        self.assertIn(f"{self.A}:{c.digest(self.OLD)} (the sentence is gone): {self.OLD}", err)

    def test_a_stale_entry_fails_until_removed(self) -> None:
        for text, reason in ((self.module("The keyed bound is proved."), "the sentence is gone"),
                             (self.module(self.OLD + " See #5293."), "now tracked")):
            with self.subTest(reason=reason):
                self.write(self.A, text)
                code, out, _ = self.run_main()
                self.assertEqual(code, 0)
                self.assertIn(f"({reason}): {self.OLD}", out)
                self.assertIn("1 stale baseline entry", out)
                code, _, err = self.run_main("--enforce")
                self.assertEqual(code, 1)
                self.assertIn(f"{self.A}:{c.digest(self.OLD)} ({reason}): {self.OLD}", err)
        (self.root / self.A).unlink()
        self.assertEqual(self.run_main("--enforce")[0], 1)
        code, out, _ = self.run_main("--update-baseline")
        self.assertEqual(code, 0)
        self.assertEqual(self.baseline(), {})
        self.assertEqual(self.run_main("--enforce")[0], 0)

    def test_update_baseline_records_new_debt_only_on_purpose(self) -> None:
        before = self.baseline()
        self.write(self.B, self.module("Depth is not certified.", "Depth is not certified."))
        code, _, err = self.run_main("--update-baseline")
        self.assertEqual(code, 1)
        self.assertIn("pass --allow-increase to record new debt on purpose", err)
        self.assertEqual(self.baseline(), before)
        code, out, _ = self.run_main("--update-baseline", "--allow-increase")
        self.assertEqual(code, 0)
        key = f"{self.B}:{c.digest('Depth is not certified.')}"
        self.assertEqual(self.baseline(), {**before, key: {"sentence": "Depth is not certified.",
                                                         "count": 2}})
        self.assertEqual(self.run_main("--enforce")[0], 0)
        # A third copy is new, and one copy fewer makes the entry stale.
        self.write(self.B, self.module(*["Depth is not certified."] * 3))
        self.assertEqual(self.run_main("--enforce")[0], 1)
        self.write(self.B, self.module("Depth is not certified."))
        code, _, err = self.run_main("--enforce")
        self.assertEqual(code, 1)
        self.assertIn("occurs untracked 1 time(s), not 2", err)

    def test_only_touched_modules_are_compared(self) -> None:
        self.write(self.B, self.module("Depth is not certified."))
        self.git("add", ".")
        self.git("commit", "-qm", "drift")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        code, out, err = self.run_main("--enforce")
        self.assertEqual((code, err), (0, ""))
        self.assertIn("Not compared: differences from the baseline in modules this change does not "
                      "touch", out)
        self.assertIn(f"{self.B}:8: t0\n    Depth is not certified.", out)
        self.assertIn("checking 0 changed module(s)", out)
        self.assertEqual(self.run_main("--all", "--enforce")[0], 1)
        # Touching the module, or the checker's baseline, compares it.
        self.write(self.B, self.module("Depth is not certified.") + "-- touched\n")
        self.assertEqual(self.run_main("--enforce")[0], 1)
        self.git("checkout", "-q", "--", self.B)
        self.write(c.BASELINE, (self.root / c.BASELINE).read_text() + "\n")
        code, out, _ = self.run_main("--enforce")
        self.assertEqual(code, 1)
        self.assertIn("so every module is compared", out)

    def test_update_baseline_leaves_other_modules_alone(self) -> None:
        self.write(self.B, self.module("Depth is not certified."))
        self.git("add", ".")
        self.git("commit", "-qm", "drift")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write(self.A, self.module("The keyed bound is proved."))
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertEqual(self.baseline(), {})

    def test_a_hand_edited_baseline_is_rejected(self) -> None:
        key = f"{self.A}:{c.digest(self.OLD)}"
        for value in ({"sentence": "Another sentence."}, {"sentence": self.OLD, "count": 1},
                      {"sentence": self.OLD, "why": "exempt"}, self.OLD):
            with self.subTest(value=value):
                self.write(c.BASELINE, json.dumps({key: value}))
                with self.assertRaises(SystemExit) as raised:
                    self.run_main()
                self.assertIn("regenerate the entry", str(raised.exception))

    def test_list_ignores_the_baseline(self) -> None:
        self.write("CslibFrontier/Crypto/Sub/D.lean", self.module("Depth is not certified. #5293"))
        code, out, _ = self.run_main("--list")
        self.assertEqual(code, 0)
        self.assertIn(f"{self.A}:8: t0: untracked\n    {self.OLD}", out)
        self.assertIn("CslibFrontier/Crypto/Sub/D.lean:8: t0: tracked by #5293", out)
        self.assertNotIn("Logic", out)
        code, out, _ = self.run_main("--list", "CslibFrontier/Crypto/Sub")
        self.assertNotIn(self.A, out)
        self.assertIn("1 disclaimer(s) under CslibFrontier/Crypto: 1 tracked", out)


if __name__ == "__main__":
    unittest.main()
