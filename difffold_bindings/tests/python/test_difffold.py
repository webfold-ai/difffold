"""Tests for the `difffold` Python module. Run with scripts/test-python.sh, which builds the
extension first. Scripts and patches are checked independently of the library: edit scripts by
rebuilding both texts by hand, patches with real `git apply`."""

import os
import random
import shutil
import subprocess
import tempfile
import threading
import unittest

import difffold


def rebuild(edits, keep):
    return "".join(line for kind, line in edits if kind in keep)


def lcs_cost(a, b):
    la, lb = a.splitlines(keepends=True), b.splitlines(keepends=True)
    dp = [[0] * (len(lb) + 1) for _ in range(len(la) + 1)]
    for i in range(1, len(la) + 1):
        for j in range(1, len(lb) + 1):
            dp[i][j] = dp[i - 1][j - 1] + 1 if la[i - 1] == lb[j - 1] else max(dp[i - 1][j], dp[i][j - 1])
    return len(la) + len(lb) - 2 * dp[-1][-1]


def rand_text(rng, final_newline):
    n = rng.randrange(25)
    return "".join(f"row {rng.randrange(6)}" + ("\n" if i + 1 < n or final_newline else "") for i in range(n))


class DiffLines(unittest.TestCase):
    def test_scripts_rebuild_both_texts_and_the_minimal_one_is_minimal(self):
        rng = random.Random(5)
        for i in range(300):
            a, b = rand_text(rng, i % 3 != 0), rand_text(rng, i % 4 != 0)
            for algo in ("minimal", "histogram"):
                e = difffold.diff_lines(a, b, algo)
                self.assertEqual(rebuild(e, ("equal", "insert")), b)
                self.assertEqual(rebuild(e, ("equal", "delete")), a)
                self.assertEqual(difffold.apply_edits(a, e), b)
            cost = sum(1 for k, _ in difffold.diff_lines(a, b) if k != "equal")
            self.assertEqual(cost, lcs_cost(a, b))

    def test_shape_and_order(self):
        e = difffold.diff_lines("a\nb\nc\n", "a\nX\nc\n")
        self.assertEqual(e, [("equal", "a\n"), ("delete", "b\n"), ("insert", "X\n"), ("equal", "c\n")])

    def test_str_gives_str_and_bytes_gives_bytes(self):
        self.assertIsInstance(difffold.diff_lines("a\n", "b\n")[0][1], str)
        e = difffold.diff_lines(b"a\n\xff\n", b"a\n\xfe\n")
        self.assertTrue(all(isinstance(line, bytes) for _, line in e))
        self.assertEqual(difffold.apply_edits(b"a\n\xff\n", e), b"a\n\xfe\n")

    def test_unicode_survives(self):
        a, b = "naïve\n日本\n", "naïve\n日本語\n"
        self.assertEqual(difffold.apply_edits(a, difffold.diff_lines(a, b)), b)

    def test_empty_and_equal(self):
        self.assertEqual(difffold.diff_lines("", ""), [])
        self.assertEqual(difffold.diff_lines("", "x\n"), [("insert", "x\n")])
        self.assertEqual(difffold.unified_patch("p\n", "p\n"), "")

    def test_large_input(self):
        a = "".join(f"line {i % 5000}\n" for i in range(60000))
        e = difffold.diff_lines(a, a + "tail\n")
        self.assertEqual(sum(1 for k, _ in e if k != "equal"), 1)

    def test_mixing_str_and_bytes_is_a_type_error(self):
        with self.assertRaises(TypeError):
            difffold.diff_lines("a\n", b"a\n")
        with self.assertRaises(TypeError):
            difffold.diff_lines(1, 2)


class ApplyEdits(unittest.TestCase):
    def test_a_script_that_does_not_fit_raises_value_error(self):
        e = difffold.diff_lines("a\nb\n", "a\nc\n")
        for old, msg in (("a\nZ\n", "does not match line 2"), ("a\n", "past the end"), ("a\nb\nx\n", "stops after 2 of 3")):
            with self.assertRaises(ValueError) as cm:
                difffold.apply_edits(old, e)
            self.assertIn(msg, str(cm.exception))

    def test_a_malformed_script_raises(self):
        with self.assertRaises(ValueError) as cm:
            difffold.apply_edits("a\n", [("move", "a\n")])
        self.assertIn("equal, delete or insert", str(cm.exception))
        with self.assertRaises(TypeError):
            difffold.apply_edits("a\n", [("equal", b"a\n")])


class UnifiedPatch(unittest.TestCase):
    def git_round_trip(self, old, new, **kw):
        patch = difffold.unified_patch(old, new, **kw)
        d = tempfile.mkdtemp()
        try:
            subprocess.run(["git", "init", "-q"], cwd=d, check=True)
            name = kw.get("name", "file")
            os.makedirs(os.path.dirname(os.path.join(d, name)) or d, exist_ok=True)
            with open(os.path.join(d, name), "w", newline="", encoding="utf-8") as f:
                f.write(old)
            with open(os.path.join(d, "p.patch"), "w", newline="", encoding="utf-8") as f:
                f.write(patch)
            zero = ["--unidiff-zero"] if kw.get("context", 3) == 0 else []

            def run(*extra):
                return subprocess.run(["git", "apply", *zero, *extra, "p.patch"], cwd=d, capture_output=True, text=True)

            r = run("--check")
            self.assertEqual(r.returncode, 0, r.stderr + patch)
            self.assertEqual(run().returncode, 0)
            with open(os.path.join(d, name), newline="", encoding="utf-8") as f:
                self.assertEqual(f.read(), new)
            self.assertEqual(run("--reverse").returncode, 0)
            with open(os.path.join(d, name), newline="", encoding="utf-8") as f:
                self.assertEqual(f.read(), old)
        finally:
            shutil.rmtree(d)

    @unittest.skipUnless(shutil.which("git"), "git not installed")
    def test_random_texts_apply_with_real_git_forwards_and_backwards(self):
        rng = random.Random(8)
        for i in range(40):
            a, b = rand_text(rng, i % 3 != 0), rand_text(rng, i % 4 != 0)
            if a != b:
                self.git_round_trip(a, b, context=i % 5, algorithm="minimal" if i % 2 else "histogram")

    @unittest.skipUnless(shutil.which("git"), "git not installed")
    def test_awkward_names_and_endings(self):
        self.git_round_trip("a\nb", "a\nb\n")
        self.git_round_trip("x\r\ny\r\n", "x\r\nz\r\n")
        for name in ("src/lib/f.rs", "my file.txt", 'q"uote.txt', "naïve-日本.txt"):
            self.git_round_trip("a\n", "b\n", name=name)


class Merge3(unittest.TestCase):
    def test_clean_and_conflicting(self):
        self.assertEqual(difffold.merge3("a\nb\nc\n", "A\nb\nc\n", "a\nb\nC\n"), ("A\nb\nC\n", 0))
        text, conflicts = difffold.merge3("a\n", "left\n", "right\n")
        self.assertEqual(conflicts, 1)
        self.assertTrue("<<<<<<<" in text and "left" in text and "right" in text)
        self.assertEqual(difffold.merge3(b"a\n", b"a\n", b"b\n"), (b"b\n", 0))


class TreeDistance(unittest.TestCase):
    ab = (["a", "b"], [-1, 0])
    wrapped = (["a", "c", "b"], [-1, 0, 1])

    def test_known_values(self):
        self.assertEqual(difffold.tree_distance(*self.ab, ["a", "c"], [-1, 0]), 1)
        # Wrapping b in c: one insert for the general objective, two for top-down.
        self.assertEqual(difffold.tree_distance(*self.ab, *self.wrapped, "general"), 1)
        self.assertEqual(difffold.tree_distance(*self.ab, *self.wrapped, "top-down"), 2)
        self.assertEqual(difffold.tree_distance(*self.ab, *self.ab), 0)

    def test_malformed_trees_raise_value_error(self):
        for labels, parents, msg in (([], [], "no nodes"), (["a"], [-1, 0], "1 labels but 2 parents"),
                                      (["a", "b"], [0, 0], "must be the root"), (["a", "b"], [-1, 1], "earlier node")):
            with self.assertRaises(ValueError) as cm:
                difffold.tree_distance(labels, parents, *self.ab)
            self.assertIn(msg, str(cm.exception))
        with self.assertRaises(ValueError):
            difffold.tree_distance(*self.ab, *self.ab, "fast")

    def test_limits_are_enforced(self):
        n = 20001
        with self.assertRaises(ValueError) as cm:
            difffold.tree_distance(["x"] * n, [-1] + [0] * (n - 1), *self.ab)
        self.assertIn("the limit is", str(cm.exception))
        # The depth limit is 8,192 here (128 on WebAssembly, which has a 1 MiB stack): 8,194 nodes
        # in a chain is one level too many.
        d = 8194
        with self.assertRaises(ValueError) as cm:
            difffold.tree_distance(["x"] * d, list(range(-1, d - 1)), *self.ab)
        self.assertIn("deeper than 8192 levels", str(cm.exception))

    def test_trees_far_deeper_than_the_wasm_limit_work(self):
        d = 2000  # WebAssembly stops at 128
        labels, parents = [f"n{i % 3}" for i in range(d)], list(range(-1, d - 1))
        other = [f"n{(i + 1) % 3}" for i in range(d)]
        for obj in ("top-down", "general"):
            self.assertGreater(difffold.tree_distance(labels, parents, other, parents, obj), 0)
            self.assertEqual(difffold.tree_distance(labels, parents, labels, parents, obj), 0)

    def test_deep_trees_do_not_depend_on_the_callers_stack(self):
        # A deep tree is compared on a thread of its own, so a caller on a small stack is safe.
        d = 2000
        labels, parents = [f"n{i % 3}" for i in range(d)], list(range(-1, d - 1))
        other = [f"n{(i + 1) % 3}" for i in range(d)]
        out = []
        old = threading.stack_size(256 * 1024)
        try:
            t = threading.Thread(
                target=lambda: out.append(difffold.tree_distance(labels, parents, other, parents, "general"))
            )
            t.start()
            t.join()
        finally:
            threading.stack_size(old)
        self.assertEqual(len(out), 1)
        self.assertGreater(out[0], 0)


class Meta(unittest.TestCase):
    def test_version(self):
        self.assertRegex(difffold.version(), r"^\d+\.\d+\.\d+")

    def test_bad_algorithm(self):
        with self.assertRaises(ValueError) as cm:
            difffold.diff_lines("a\n", "b\n", "fast")
        self.assertIn("minimal or histogram", str(cm.exception))


if __name__ == "__main__":
    unittest.main()
