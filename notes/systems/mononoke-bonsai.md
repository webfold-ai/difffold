# Meta Mononoke and the Bonsai changeset model

URLs fetched 2026-11-03 (raw files from the facebook/sapling repository, main branch):
- https://raw.githubusercontent.com/facebook/sapling/main/eden/mononoke/docs/README.md
- .../2.1-bonsai-data-model.md
- .../2.3-derived-data.md
FULL TEXT of those three docs (read in full: 2.1 and the first ~70 non-blank lines of 2.3). NOT read: 2.2 facets, 2.4 storage, 4.x pushrebase and cross-repo sync, and any Meta engineering blog posts or the original Bonsai design write-ups. I did not find or fetch an engineering-blog post; every claim here comes from the in-repo docs. These docs are current-main descriptions, possibly newer than Scion's 2026 reference; they were written for "developers, operators, and AI agents".

## Mechanism
- Inherent vs derived: "Inherent data constitutes the core Merkle DAG and serves as the source of truth ... Bonsai changesets, File content blobs, Original VCS bytes". "Derived data comprises indexes and representations computed from inherent data. This data is not included in content-addressed hashes and can be regenerated from inherent data." "The write path stores only inherent data, keeping the critical section minimal."
- Bonsai changeset: parents, author, committer, message, VCS-specific extras, and "a flat list of path-to-change mappings". Changes: tracked change (content identifier, file type, size, optional copy-from), tracked deletion, untracked change (snapshots). "Copy-from information explicitly records file copies and renames, referencing the source path and changeset." Contrast: "This differs from Git's nested tree structure and Mercurial's manifest system."
- Hashing: Blake2b, 256-bit. ChangesetId = hash of the serialised changeset (Thrift compact), so depends on parents, metadata, file changes. "File contents are hashed separately ... to produce a ContentId. Identical files across different commits or repositories produce the same content identifier, enabling deduplication." (Note: the name ContentId is Mononoke's own term for the content hash; our ContentId is for canonical subtree content, not file bytes.)
- Derived data framework (`BonsaiDerivable`): `derive_single` "Compute derived data for one changeset given its Bonsai representation and the derived data for its parents"; `store_mapping`, `fetch`; batch variants; a declared `Dependencies` type forming a DAG of derived types ("Blame depends on Unodes"). Read path: "Check if derived data exists for the requested changeset ... If not derived, compute it." Derivation is "asynchronous by background workers or on-demand".
- Storage keys of derived data include the changeset id, e.g. `derived_root_blame_v2.<ChangesetId>`.

## Stated limits
- The docs are architectural; they give no benchmark numbers in what I read. Bonsai's `git_tree_hash` field is "Not used (deprecated)". Rename/copy information is whatever the committing client recorded or inferred at commit time; Bonsai stores it but does not assert it is correct.

## Lessons
- Explicit copy-from in the changeset is the closest prior art to our "record edits when they happen": a rename/copy is an assertion by the committer, recorded once, not re-inferred from similarity at every diff. It is also an assertion that can be wrong, so provenance (who asserted it) is worth storing.
- Two-hash design (ChangesetId over the whole commit; ContentId over bytes) mirrors our ContentId/VersionId split. Bonsai has no OccurrenceId: file identity across a rename is the path plus an optional copy-from edge, which is a per-commit pointer rather than a durable entity id. This is the gap OccurrenceId fills, and it is why it is "not yet implemented": nobody in this lineage has a stable occurrence identity, only edges.
- Derived data is excluded from the content hash and regenerable. Our presented delta and inferred correspondences should likewise be outside VersionId's hash.
- Mononoke, like Scion, owns the write path; a pushed commit is the authority.
