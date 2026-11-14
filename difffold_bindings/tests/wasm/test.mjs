// Tests for the WebAssembly build. Run `scripts/build-wasm.sh` first, then `node tests/wasm/test.mjs`.
// Edit scripts are rebuilt by hand; patches go through real `git apply`.
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createRequire } from "node:module";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const require = createRequire(import.meta.url);
const d = require("../../dist/difffold_bindings.js");

let seed = 5;
const rnd = (n) => ((seed = (seed * 1103515245 + 12345) & 0x7fffffff) % n);
const randText = (finalNewline) => {
  const n = rnd(25);
  let t = "";
  for (let i = 0; i < n; i++) t += `row ${rnd(6)}` + (i + 1 < n || finalNewline ? "\n" : "");
  return t;
};
const rebuild = (edits, keep) => edits.filter(([k]) => keep.includes(k)).map(([, l]) => l).join("");
const lcsCost = (a, b) => {
  const la = a.match(/[^\n]*\n|[^\n]+/g) ?? [], lb = b.match(/[^\n]*\n|[^\n]+/g) ?? [];
  const dp = Array.from({ length: la.length + 1 }, () => new Array(lb.length + 1).fill(0));
  for (let i = 1; i <= la.length; i++)
    for (let j = 1; j <= lb.length; j++)
      dp[i][j] = la[i - 1] === lb[j - 1] ? dp[i - 1][j - 1] + 1 : Math.max(dp[i - 1][j], dp[i][j - 1]);
  return la.length + lb.length - 2 * dp[la.length][lb.length];
};

// line diff: scripts rebuild both texts; the minimal one is minimal
for (let i = 0; i < 300; i++) {
  const a = randText(i % 3 !== 0), b = randText(i % 4 !== 0);
  for (const algo of ["minimal", "histogram"]) {
    const e = d.diffLinesText(a, b, algo);
    assert.equal(rebuild(e, ["equal", "insert"]), b);
    assert.equal(rebuild(e, ["equal", "delete"]), a);
    assert.equal(d.applyEditsText(a, e), b);
  }
  const cost = d.diffLinesText(a, b, "minimal").filter(([k]) => k !== "equal").length;
  assert.equal(cost, lcsCost(a, b));
}
assert.deepEqual(d.diffLinesText("a\nb\nc\n", "a\nX\nc\n", "minimal"),
  [["equal", "a\n"], ["delete", "b\n"], ["insert", "X\n"], ["equal", "c\n"]]);

// bytes form, including bytes that are not UTF-8
const enc = new TextEncoder();
const ba = new Uint8Array([0x61, 10, 0xff, 10]), bb = new Uint8Array([0x61, 10, 0xfe, 10]);
const be = d.diffLines(ba, bb, "minimal");
assert.ok(be[0][1] instanceof Uint8Array);
assert.deepEqual([...d.applyEdits(ba, be)], [...bb]);
assert.equal(d.diffLines(enc.encode(""), enc.encode(""), "minimal").length, 0);

// unicode, empty, large
assert.equal(d.applyEditsText("naïve\n日本\n", d.diffLinesText("naïve\n日本\n", "naïve\n日本語\n", "minimal")), "naïve\n日本語\n");
const big = Array.from({ length: 60000 }, (_, i) => `line ${i % 5000}\n`).join("");
assert.equal(d.diffLinesText(big, big + "tail\n", "minimal").filter(([k]) => k !== "equal").length, 1);

// scripts that do not fit, and malformed scripts, are errors
const e2 = d.diffLinesText("a\nb\n", "a\nc\n", "minimal");
assert.throws(() => d.applyEditsText("a\nZ\n", e2), /does not match line 2/);
assert.throws(() => d.applyEditsText("a\n", e2), /past the end/);
assert.throws(() => d.applyEditsText("a\nb\nx\n", e2), /stops after 2 of 3/);
assert.throws(() => d.applyEditsText("a\n", [["move", "a\n"]]), /equal, delete or insert/);
assert.throws(() => d.applyEditsText("a\n", [["equal", new Uint8Array([97])]]), /must be a string/);
assert.throws(() => d.applyEditsText("a\n", ["nope"]), /pair/);
assert.throws(() => d.diffLinesText("a\n", "b\n", "fast"), (e) => e instanceof Error && /minimal or histogram/.test(e.message));

// unified patch through real git, forwards and backwards
const gitRoundTrip = (oldT, newT, name = "file", context = 3, algo = "minimal") => {
  const patch = d.unifiedPatchText(oldT, newT, name, context, algo);
  const dir = mkdtempSync(join(tmpdir(), "dfb-"));
  try {
    const git = (...a) => execFileSync("git", a, { cwd: dir, stdio: "pipe" });
    git("init", "-q");
    writeFileSync(join(dir, "f"), oldT);
    writeFileSync(join(dir, "p.patch"), patch);
    const z = context === 0 ? ["--unidiff-zero"] : [];
    // `name` may contain a path; the patch names it, so write the old text there.
    const target = join(dir, name);
    execFileSync("mkdir", ["-p", join(target, "..")]);
    writeFileSync(target, oldT);
    git("apply", ...z, "--check", "p.patch");
    git("apply", ...z, "p.patch");
    assert.equal(readFileSync(target, "utf8"), newT);
    git("apply", ...z, "--reverse", "p.patch");
    assert.equal(readFileSync(target, "utf8"), oldT);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
};
for (let i = 0; i < 30; i++) {
  const a = randText(i % 3 !== 0), b = randText(i % 4 !== 0);
  if (a !== b) gitRoundTrip(a, b, "file", i % 5, i % 2 ? "minimal" : "histogram");
}
gitRoundTrip("a\nb", "a\nb\n");
gitRoundTrip("x\r\ny\r\n", "x\r\nz\r\n");
for (const n of ["src/lib/f.rs", "my file.txt", 'q"uote.txt', "naïve-日本.txt"]) gitRoundTrip("a\n", "b\n", n);
assert.equal(d.unifiedPatchText("p\n", "p\n", "f", 3, "minimal"), "");
assert.ok(d.unifiedPatch(enc.encode("a\n"), enc.encode("b\n"), "f", 3, "minimal") instanceof Uint8Array);

// merge
assert.deepEqual(d.merge3Text("a\nb\nc\n", "A\nb\nc\n", "a\nb\nC\n", "minimal"), ["A\nb\nC\n", 0]);
const [mt, mc] = d.merge3Text("a\n", "left\n", "right\n", "minimal");
assert.equal(mc, 1);
assert.match(mt, /<<<<<<</);
const [mb, mbc] = d.merge3(enc.encode("a\n"), enc.encode("a\n"), enc.encode("b\n"), "minimal");
assert.equal(new TextDecoder().decode(mb), "b\n");
assert.equal(mbc, 0);

// trees
const I = (a) => Int32Array.from(a);
assert.equal(d.treeDistance(["a", "b"], I([-1, 0]), ["a", "c"], I([-1, 0]), "top-down"), 1);
assert.equal(d.treeDistance(["a", "b"], I([-1, 0]), ["a", "c", "b"], I([-1, 0, 1]), "general"), 1);
assert.equal(d.treeDistance(["a", "b"], I([-1, 0]), ["a", "c", "b"], I([-1, 0, 1]), "top-down"), 2);
const ab = [["a", "b"], I([-1, 0])];
assert.throws(() => d.treeDistance([], I([]), ...ab, "general"), /no nodes/);
assert.throws(() => d.treeDistance(["a", "b"], I([0, 0]), ...ab, "general"), /must be the root/);
assert.throws(() => d.treeDistance(["a", "b"], I([-1, 1]), ...ab, "general"), /earlier node/);
assert.throws(() => d.treeDistance(["a"], I([-1]), ...ab, "fast"), /top-down or general/);
const n = 20001;
assert.throws(() => d.treeDistance(new Array(n).fill("x"), I([-1, ...new Array(n - 1).fill(0)]), ...ab, "top-down"), /the limit is/);
assert.throws(() => d.treeDistance(new Array(130).fill("x"), I(Array.from({ length: 130 }, (_, i) => i - 1)), ...ab, "top-down"), /deeper than/);
// the deepest allowed tree, on WebAssembly's own 1 MiB stack
const depth = 129, chain = I(Array.from({ length: depth }, (_, i) => i - 1));
const l1 = Array.from({ length: depth }, (_, i) => `n${i % 3}`), l2 = Array.from({ length: depth }, (_, i) => `n${(i + 1) % 3}`);
for (const o of ["top-down", "general"]) assert.ok(d.treeDistance(l1, chain, l2, chain, o) > 0);

assert.match(d.version(), /^\d+\.\d+\.\d+/);
console.log("wasm: all tests passed");
