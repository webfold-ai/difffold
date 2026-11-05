#!/usr/bin/env python3
"""Generates synthetic tree pairs for the fastted benchmark.

usage: gen_synthetic.py OUTDIR

Writes OUTDIR/syn/<pair>/a.tree and b.tree in the postorder format read by fastted_bench and the C++
adapters (see tools/fastted_adapters/tree_io.h), and OUTDIR/syn_pairs.tsv with one row per pair.

Shapes (the first tree of every pair): chain, star (wide), left comb, right comb, balanced binary.
Regimes:
  mut    low-distance: the second tree is the first with max(1, n // 100) random edits
         (relabel, insert a leaf, delete a leaf).
  unrel  large-distance: the second tree is a uniform random recursive tree with n nodes and fresh labels.
Sizes: 100, 1000, 5000 nodes. Labels are drawn from a 16-symbol alphabet. Seeds are fixed per pair.
"""
import os
import random
import sys

ALPHABET = 16
SIZES = (100, 1000, 5000)
SHAPES = ("chain", "star", "lcomb", "rcomb", "balanced")


def shape_children(shape, n):
    kids = [[] for _ in range(n)]
    if shape == "chain":
        for i in range(n - 1):
            kids[i] = [i + 1]
    elif shape == "star":
        kids[0] = list(range(1, n))
    elif shape in ("lcomb", "rcomb"):
        cur, nxt = 0, 1
        while nxt < n:
            if n - nxt >= 2:
                leaf, spine = nxt, nxt + 1
                nxt += 2
                kids[cur] = [spine, leaf] if shape == "lcomb" else [leaf, spine]
                cur = spine
            else:
                kids[cur] = [nxt]
                nxt += 1
    elif shape == "balanced":
        for i in range(n):
            for c in (2 * i + 1, 2 * i + 2):
                if c < n:
                    kids[i].append(c)
    else:
        raise ValueError(shape)
    return kids


def random_recursive(n, rng):
    kids = [[] for _ in range(n)]
    for i in range(1, n):
        kids[rng.randrange(i)].append(i)
    return kids


class Tree:
    def __init__(self, children, labels, root=0):
        self.children = {i: list(c) for i, c in enumerate(children)}
        self.labels = {i: labels[i] for i in range(len(children))}
        self.root = root

    def mutate(self, k, rng):
        for _ in range(k):
            leaves = [v for v, c in self.children.items() if not c and v != self.root]
            op = rng.random()
            if op < 0.5 or not leaves:
                v = rng.choice(list(self.labels))
                new = rng.randrange(ALPHABET - 1)
                self.labels[v] = new + 1 if new >= self.labels[v] else new
            elif op < 0.75:
                parent = rng.choice(list(self.children))
                new_id = max(self.children) + 1
                self.children[new_id] = []
                self.labels[new_id] = rng.randrange(ALPHABET)
                pos = rng.randrange(len(self.children[parent]) + 1)
                self.children[parent].insert(pos, new_id)
            else:
                v = rng.choice(leaves)
                for c in self.children.values():
                    if v in c:
                        c.remove(v)
                        break
                del self.children[v]
                del self.labels[v]
        return self

    def postorder_text(self):
        order = []
        stack = [(self.root, False)]
        while stack:
            v, expanded = stack.pop()
            if expanded:
                order.append(v)
            else:
                stack.append((v, True))
                for c in reversed(self.children[v]):
                    stack.append((c, False))
        index = {v: i for i, v in enumerate(order)}
        parent = {}
        for v in order:
            for c in self.children[v]:
                parent[c] = index[v]
        lines = [str(len(order))]
        for v in order:
            lines.append(f"{self.labels[v]} {parent.get(v, -1)}")
        return "\n".join(lines) + "\n", len(order)


def main():
    out = sys.argv[1]
    syn = os.path.join(out, "syn")
    os.makedirs(syn, exist_ok=True)
    rows = ["pair\tregime\tshape\tnominal_n\tnodes_a\tnodes_b\tpath"]
    for regime in ("mut", "unrel"):
        for shape in SHAPES:
            for n in SIZES:
                rng = random.Random(f"{regime}-{shape}-{n}")
                labels = [rng.randrange(ALPHABET) for _ in range(n)]
                a = Tree(shape_children(shape, n), labels)
                if regime == "mut":
                    b = Tree(
                        [list(a.children[i]) for i in range(n)],
                        [a.labels[i] for i in range(n)],
                    ).mutate(max(1, n // 100), rng)
                else:
                    b_labels = [rng.randrange(ALPHABET) for _ in range(n)]
                    b = Tree(random_recursive(n, rng), b_labels)
                name = f"syn-{regime}-{shape}-{n}"
                d = os.path.join(syn, name)
                os.makedirs(d, exist_ok=True)
                ta, na = a.postorder_text()
                tb, nb = b.postorder_text()
                with open(os.path.join(d, "a.tree"), "w") as f:
                    f.write(ta)
                with open(os.path.join(d, "b.tree"), "w") as f:
                    f.write(tb)
                rows.append(f"{name}\t{regime}\t{shape}\t{n}\t{na}\t{nb}\t{d}")
    with open(os.path.join(out, "syn_pairs.tsv"), "w") as f:
        f.write("\n".join(rows) + "\n")


if __name__ == "__main__":
    main()
