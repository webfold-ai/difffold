// Reads the tree files written by fastted_export and gen_synthetic.py.
//
// A tree file starts with the node count n, then n lines `label parent` in postorder. `parent` is the
// postorder index of the parent, or -1 for the root (always the last node). Children keep their
// postorder order, which is their left-to-right order.
#ifndef FASTTED_TREE_IO_H
#define FASTTED_TREE_IO_H

#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

struct FileTree {
    std::vector<long long> label;
    std::vector<long long> parent;
    std::vector<std::vector<int>> kids;  // postorder child indices, left to right
};

inline FileTree read_tree(const std::string& path) {
    FileTree t;
    FILE* f = std::fopen(path.c_str(), "r");
    if (f == nullptr) {
        std::fprintf(stderr, "cannot open %s\n", path.c_str());
        std::exit(2);
    }
    long long n = 0;
    if (std::fscanf(f, "%lld", &n) != 1) {
        std::fprintf(stderr, "bad count in %s\n", path.c_str());
        std::exit(2);
    }
    t.label.resize(static_cast<size_t>(n));
    t.parent.resize(static_cast<size_t>(n));
    for (long long i = 0; i < n; ++i) {
        if (std::fscanf(f, "%lld %lld", &t.label[static_cast<size_t>(i)], &t.parent[static_cast<size_t>(i)]) != 2) {
            std::fprintf(stderr, "bad row %lld in %s\n", i, path.c_str());
            std::exit(2);
        }
    }
    std::fclose(f);
    t.kids.assign(static_cast<size_t>(n), {});
    for (long long i = 0; i < n; ++i) {
        const long long p = t.parent[static_cast<size_t>(i)];
        if (p >= 0) {
            t.kids[static_cast<size_t>(p)].push_back(static_cast<int>(i));
        }
    }
    return t;
}

#endif  // FASTTED_TREE_IO_H
