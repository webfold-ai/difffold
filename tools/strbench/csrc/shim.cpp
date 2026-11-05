// Plain-C entry points over Edlib and WFA2-lib so the Rust harness can call them
// with byte slices. Both wrappers use exact global (end-to-end) unit-cost
// Levenshtein distance. Return values: >= 0 is the distance, -1 means the
// distance exceeds the bound, -2 means the library reported an error.

#include <climits>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstdint>

#include "edlib.h"

extern "C" {
#include "wavefront/wfa.h"
}

extern "C" int64_t sb_edlib(const uint8_t* a, size_t an, const uint8_t* b, size_t bn, int64_t k) {
	if (an > INT_MAX || bn > INT_MAX || k > INT_MAX) {
		return -2;
	}
	EdlibAlignConfig cfg = edlibNewAlignConfig(k < 0 ? -1 : static_cast<int>(k), EDLIB_MODE_NW,
	                                           EDLIB_TASK_DISTANCE, nullptr, 0);
	EdlibAlignResult r = edlibAlign(reinterpret_cast<const char*>(a), static_cast<int>(an),
	                                reinterpret_cast<const char*>(b), static_cast<int>(bn), cfg);
	int64_t out;
	if (r.status != EDLIB_STATUS_OK) {
		out = -2;
	} else if (r.editDistance < 0) {
		out = -1;
	} else {
		out = r.editDistance;
	}
	edlibFreeAlignResult(r);
	return out;
}

extern "C" int64_t sb_wfa(const uint8_t* a, size_t an, const uint8_t* b, size_t bn, int64_t max_steps) {
	if (an > INT_MAX || bn > INT_MAX) {
		return -2;
	}
	wavefront_aligner_attr_t attr = wavefront_aligner_attr_default;
	attr.distance_metric = edit;
	attr.alignment_scope = compute_score;
	attr.heuristic.strategy = wf_heuristic_none;
	// WFA2 aborts once `score >= max_alignment_steps`, so the bound k is passed as k + 1
	// to let an alignment of cost exactly k finish.
	if (max_steps < 0 || max_steps >= INT_MAX - 1) {
		attr.system.max_alignment_steps = INT_MAX;
	} else {
		attr.system.max_alignment_steps = static_cast<int>(max_steps) + 1;
	}
	wavefront_aligner_t* wf = wavefront_aligner_new(&attr);
	wavefront_align(wf, reinterpret_cast<const char*>(a), static_cast<int>(an),
	                reinterpret_cast<const char*>(b), static_cast<int>(bn));
	int64_t out;
	if (wf->align_status.status == WF_STATUS_ALG_COMPLETED) {
		out = wf->cigar->score;
	} else if (wf->align_status.status == WF_STATUS_MAX_STEPS_REACHED) {
		out = -1;
	} else {
		out = -2;
	}
	wavefront_aligner_delete(wf);
	return out;
}
