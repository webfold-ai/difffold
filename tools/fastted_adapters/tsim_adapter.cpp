// Times tree-similarity (DatabaseGroup/tree-similarity) on tree files, with unit costs.
//
// Built against the library's header-only sources. Set TREE_SIMILARITY_DIR to a checkout at the
// 0.1.1 tag. Build with tools/fastted_adapters/build.sh.
//
// usage: tsim_adapter --tool apted|touzet_baseline|touzet_krset|touzet_dp
//                     --mode unknown|threshold [--tau T] [--reps R] --pair NAME <a.tree> <b.tree>
//
// `unknown` calls the algorithm's ted(), which searches the threshold itself (for the Touzet family
// that is the doubling loop in ted_algorithm_touzet.h). `threshold` calls ted_k(a, b, tau) for the
// Touzet family. APTED has no threshold entry point, so it only runs in unknown mode.
//
// Prints CSV rows `tool,mode,pair,phase,rep,us,distance,status`. Phases: `build` (constructing the
// library's node tree from the file; the library's add_child copies subtrees), `index` (index_tree
// for both trees), `dist` (the distance call). Rep 0 is an untimed warm-up with status `warmup`.
// A run over 60 s prints a `gt60s` row and stops.

#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "apted_tree_index.h"
#include "node.h"
#include "string_label.h"
#include "tree_indexer.h"
#include "touzet_baseline_tree_index.h"
#include "touzet_depth_pruning_truncated_tree_fix_tree_index.h"
#include "touzet_kr_set_tree_index.h"
#include "unit_cost_model.h"

#include "tree_io.h"

using Clock = std::chrono::steady_clock;
using Label = label::StringLabel;
using LD = label::LabelDictionary<Label>;
using CostModel = cost_model::UnitCostModelLD<Label>;
using NodeT = node::Node<Label>;

namespace {

const long long kCellLimitUs = 60LL * 1000 * 1000;

struct Options {
    std::string tool = "apted";
    std::string mode = "unknown";
    double tau = -1;
    int reps = 7;
    std::string pair = "pair";
    std::string a;
    std::string b;
};

Options parse_args(int argc, char** argv) {
    Options o;
    std::vector<std::string> files;
    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        if (arg == "--tool" && i + 1 < argc) {
            o.tool = argv[++i];
        } else if (arg == "--mode" && i + 1 < argc) {
            o.mode = argv[++i];
        } else if (arg == "--tau" && i + 1 < argc) {
            o.tau = std::atof(argv[++i]);
        } else if (arg == "--reps" && i + 1 < argc) {
            o.reps = std::atoi(argv[++i]);
        } else if (arg == "--pair" && i + 1 < argc) {
            o.pair = argv[++i];
        } else {
            files.push_back(arg);
        }
    }
    if (files.size() != 2) {
        std::fprintf(stderr, "usage: tsim_adapter --tool T --mode unknown|threshold [--tau T] [--reps R] --pair P a.tree b.tree\n");
        std::exit(2);
    }
    o.a = files[0];
    o.b = files[1];
    if (o.mode != "unknown" && o.mode != "threshold") {
        std::fprintf(stderr, "mode must be unknown or threshold\n");
        std::exit(2);
    }
    return o;
}

// Builds the library's node tree bottom-up. Each add_child call copies the child subtree, which is part
// of this library's construction cost and is reported in the `build` phase.
NodeT build_root(const FileTree& t) {
    const size_t n = t.label.size();
    std::vector<std::unique_ptr<NodeT>> slot(n);
    for (size_t i = 0; i < n; ++i) {
        auto cur = std::make_unique<NodeT>(Label(std::to_string(t.label[i])));
        for (int c : t.kids[i]) {
            cur->add_child(*slot[static_cast<size_t>(c)]);
            slot[static_cast<size_t>(c)].reset();
        }
        slot[i] = std::move(cur);
    }
    return *slot[n - 1];
}

void print_row(const Options& o, const char* phase, int rep, long long us, const std::string& dist, const char* status) {
    std::printf("%s,%s,%s,%s,%d,%lld,%s,%s\n", o.tool.c_str(), o.mode.c_str(), o.pair.c_str(), phase, rep, us, dist.c_str(), status);
}

template <typename TI, typename Alg, typename DistFn>
void bench(const Options& o, const FileTree& fa, const FileTree& fb, DistFn dist) {
    for (int rep = 0; rep <= o.reps; ++rep) {
        const bool warm = rep == 0;
        const char* ok = warm ? "warmup" : "ok";

        auto t0 = Clock::now();
        NodeT ra = build_root(fa);
        NodeT rb = build_root(fb);
        auto t1 = Clock::now();

        LD ld;
        CostModel ucm(ld);
        TI ta;
        TI tb;
        node::index_tree(ta, ra, ld, ucm);
        node::index_tree(tb, rb, ld, ucm);
        auto t2 = Clock::now();

        Alg alg(ucm);
        double d = dist(alg, ta, tb);
        auto t3 = Clock::now();

        const long long build_us = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count();
        const long long index_us = std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1).count();
        const long long dist_us = std::chrono::duration_cast<std::chrono::microseconds>(t3 - t2).count();

        print_row(o, "build", rep, build_us, "", ok);
        print_row(o, "index", rep, index_us, "", ok);
        if (std::isinf(d)) {
            print_row(o, "dist", rep, dist_us, "NA", warm ? "warmup" : "above_tau");
        } else {
            print_row(o, "dist", rep, dist_us, std::to_string(static_cast<long long>(std::llround(d))), ok);
        }

        const long long total_us = build_us + index_us + dist_us;
        if (total_us > kCellLimitUs) {
            print_row(o, "dist", rep, dist_us, "NA", "gt60s");
            return;
        }
    }
}

}  // namespace

int main(int argc, char** argv) {
    const Options o = parse_args(argc, argv);
    const FileTree fa = read_tree(o.a);
    const FileTree fb = read_tree(o.b);
    const bool threshold = o.mode == "threshold";
    const int tau = static_cast<int>(o.tau);

    if (o.tool == "apted") {
        if (threshold) {
            std::fprintf(stderr, "apted has no threshold entry point\n");
            return 2;
        }
        using Alg = ted::APTEDTreeIndex<CostModel, node::TreeIndexAPTED>;
        bench<node::TreeIndexAPTED, Alg>(o, fa, fb, [](Alg& alg, const node::TreeIndexAPTED& x, const node::TreeIndexAPTED& y) {
            return alg.ted(x, y);
        });
    } else if (o.tool == "touzet_baseline") {
        using Alg = ted::TouzetBaselineTreeIndex<CostModel, node::TreeIndexTouzetBaseline>;
        bench<node::TreeIndexTouzetBaseline, Alg>(o, fa, fb, [threshold, tau](Alg& alg, const node::TreeIndexTouzetBaseline& x, const node::TreeIndexTouzetBaseline& y) {
            return threshold ? alg.ted_k(x, y, tau) : alg.ted(x, y);
        });
    } else if (o.tool == "touzet_krset") {
        using Alg = ted::TouzetKRSetTreeIndex<CostModel, node::TreeIndexTouzetKRSet>;
        bench<node::TreeIndexTouzetKRSet, Alg>(o, fa, fb, [threshold, tau](Alg& alg, const node::TreeIndexTouzetKRSet& x, const node::TreeIndexTouzetKRSet& y) {
            return threshold ? alg.ted_k(x, y, tau) : alg.ted(x, y);
        });
    } else if (o.tool == "touzet_dp") {
        using Alg = ted::TouzetDepthPruningTruncatedTreeFixTreeIndex<CostModel, node::TreeIndexTouzetDepthPruningTruncatedTreeFix>;
        bench<node::TreeIndexTouzetDepthPruningTruncatedTreeFix, Alg>(o, fa, fb, [threshold, tau](Alg& alg, const node::TreeIndexTouzetDepthPruningTruncatedTreeFix& x, const node::TreeIndexTouzetDepthPruningTruncatedTreeFix& y) {
            return threshold ? alg.ted_k(x, y, tau) : alg.ted(x, y);
        });
    } else {
        std::fprintf(stderr, "unknown tool %s\n", o.tool.c_str());
        return 2;
    }
    return 0;
}
