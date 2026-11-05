// Times X-TED CPU (Davis-Fan/X-TED, X-TED_CPU/) on tree files, with unit costs.
//
// Links X-TED's TED.cpp, parallel_computing.cpp and dataset_preprocess.cpp, not its main.cpp or TED_test.cpp,
// because those define a fixed driver. X-TED's standard_ted takes labels and adjacency lists in preorder with
// children in left-to-right order, so this adapter converts the postorder tree file to that layout in the
// `build` phase. X-TED prints its own timing lines to std::cout, which this adapter redirects to /dev/null.
//
// usage: xted_adapter --mode unknown [--threads N] [--reps R] --pair NAME <a.tree> <b.tree>
// The tool column is xted-tN, where N is the thread count passed to standard_ted.
//
// X-TED has no threshold entry point, so only unknown mode exists. Its internal cost matrix and key-root
// setup run inside standard_ted and are therefore part of the `dist` phase. Build with build.sh.
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include "TED_C++.h"
#include "tree_io.h"

using Clock = std::chrono::steady_clock;

namespace {

const long long kCellLimitUs = 60LL * 1000 * 1000;

struct Preorder {
    std::vector<std::string> node;
    std::vector<std::vector<int>> adj;
};

// Converts a postorder tree to preorder with children in left-to-right order (X-TED's numbering).
Preorder to_preorder(const FileTree& t) {
    const size_t n = t.label.size();
    std::vector<int> order;
    order.reserve(n);
    std::vector<int> newid(n, -1);
    std::vector<int> stack{static_cast<int>(n) - 1};
    while (!stack.empty()) {
        const int v = stack.back();
        stack.pop_back();
        newid[static_cast<size_t>(v)] = static_cast<int>(order.size());
        order.push_back(v);
        const auto& kids = t.kids[static_cast<size_t>(v)];
        for (auto it = kids.rbegin(); it != kids.rend(); ++it) {
            stack.push_back(*it);
        }
    }
    Preorder p;
    p.node.resize(n);
    p.adj.assign(n, {});
    for (size_t k = 0; k < n; ++k) {
        const size_t v = static_cast<size_t>(order[k]);
        p.node[k] = std::to_string(t.label[v]);
        for (int c : t.kids[v]) {
            p.adj[k].push_back(newid[static_cast<size_t>(c)]);
        }
    }
    return p;
}

void print_row(const std::string& tool, const std::string& mode, const std::string& pair, const char* phase, int rep, long long us, const std::string& dist, const char* status) {
    std::printf("%s,%s,%s,%s,%d,%lld,%s,%s\n", tool.c_str(), mode.c_str(), pair.c_str(), phase, rep, us, dist.c_str(), status);
}

}  // namespace

int main(int argc, char** argv) {
    std::string tool = "xted";
    std::string mode = "unknown";
    std::string pair = "pair";
    int reps = 7;
    int threads = 1;
    std::vector<std::string> files;
    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        if (arg == "--tool" && i + 1 < argc) {
            tool = argv[++i];
        } else if (arg == "--mode" && i + 1 < argc) {
            mode = argv[++i];
        } else if (arg == "--reps" && i + 1 < argc) {
            reps = std::atoi(argv[++i]);
        } else if (arg == "--pair" && i + 1 < argc) {
            pair = argv[++i];
        } else if (arg == "--threads" && i + 1 < argc) {
            threads = std::atoi(argv[++i]);
        } else {
            files.push_back(arg);
        }
    }
    if (threads < 1) {
        std::fprintf(stderr, "--threads must be at least 1\n");
        return 2;
    }
    // The thread count is part of the tool name so single- and multi-thread rows stay distinct in the CSV.
    tool = "xted-t" + std::to_string(threads);
    if (files.size() != 2 || mode != "unknown") {
        std::fprintf(stderr, "usage: xted_adapter --mode unknown [--reps R] --pair P a.tree b.tree\n");
        return 2;
    }

    // Restore std::cout before returning: the null stream is a local and must not outlive the redirect.
    std::ofstream devnull("/dev/null");
    std::streambuf* saved_cout = std::cout.rdbuf(devnull.rdbuf());

    const FileTree fa = read_tree(files[0]);
    const FileTree fb = read_tree(files[1]);

    for (int rep = 0; rep <= reps; ++rep) {
        const bool warm = rep == 0;
        const char* ok = warm ? "warmup" : "ok";

        auto t0 = Clock::now();
        Preorder pa = to_preorder(fa);
        Preorder pb = to_preorder(fb);
        auto t1 = Clock::now();

        // standard_ted clears the label vectors it receives, so the tree copies are consumed each run.
        const int d = standard_ted(pa.node, pa.adj, pb.node, pb.adj, threads, 1);
        auto t2 = Clock::now();

        const long long build_us = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count();
        const long long dist_us = std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1).count();
        print_row(tool, mode, pair, "build", rep, build_us, "", ok);
        print_row(tool, mode, pair, "dist", rep, dist_us, std::to_string(d), ok);

        if (build_us + dist_us > kCellLimitUs) {
            print_row(tool, mode, pair, "dist", rep, dist_us, "NA", "gt60s");
            break;
        }
    }
    std::cout.rdbuf(saved_cout);
    return 0;
}
