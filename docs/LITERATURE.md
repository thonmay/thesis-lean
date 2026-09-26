# Literature and provenance (P0)

This file records the P0 literature gate from the supervisor roadmap
(`docs/ROADMAP-palomar-v4-arxiv-vibemathed.md`). It is the evidence base for
the provenance notes in `formalization.yaml` and for the related-work framing
of the eventual arXiv preprint (P4). Every claim below is tagged:

- **VERIFIED** — citation checked against the publisher record (DOI resolves,
  venue/year/pages confirmed).
- **NOT FOUND** — searched the listed sources and found no prior statement of
  the specific result. This is an absence of evidence, not proof of absence;
  the wording in `formalization.yaml` reflects that ("we are not aware", never
  "no such result exists").

## 1. Foundations (VERIFIED)

These are the classical works the formalization builds on. All four citations
were re-checked against their DOIs.

| Work | Cite | Role here |
|------|------|-----------|
| Rose, Tarjan, Lueker | *Algorithmic Aspects of Vertex Elimination on Graphs.* SIAM J. Comput. 5(2):266-283, 1976. doi:10.1137/0205021 | Introduced LexBFS and linear-time chordal recognition. |
| Tarjan, Yannakakis | *Simple Linear-Time Algorithms to Test Chordality of Graphs...* SIAM J. Comput. 13(3):566-579, 1984. doi:10.1137/0213035 | Introduced Maximum Cardinality Search (MCS) as a "simple alternative" to LexBFS. The MCS definition used here is from this paper. |
| Corneil, Krueger | *A Unified View of Graph Searching.* SIAM J. Discrete Math. 22(4):1259-1276, 2008. doi:10.1137/050623498 | Vertex-ordering characterizations of MCS, LexBFS, BFS, DFS, MNS; both MCS and LexBFS are restrictions of maximal neighborhood search, neither containing the other. Basis for the incomparability statement in the README. |
| Berry, Blair, Heggernes, Peyton | *Maximum Cardinality Search for Computing Minimal Triangulations of Graphs.* Algorithmica 39(4):287-298, 2004. | Introduced MCS-M (multi-sweep MCS) for chordal completion. Background only. |

The MCS-M paper (Berry-Blair-Heggernes-Peyton, Algorithmica 39(4):287-298,
2004) is cited only as background on MCS variants; this formalization uses the
single-sweep MCS of Tarjan-Yannakakis (1984).

### MCS vs LexBFS: incomparable, even on chordal graphs (VERIFIED by counterexample)

Earlier drafts stated "MCS is a superset of LexBFS on chordal graphs." This is
**false**, and was corrected in this commit. The two search families are
incomparable on general graphs *and* on chordal graphs. Witness (chordal,
7 vertices): a 5-clique on {1,2,3,4,5}, plus a vertex `u` joined to `1`, plus a
vertex `v` joined to `2` and `3`. Brute-force enumeration of both ordering
families (all tie-breaks) gives 204 orderings each, with a symmetric difference
of 40 orderings on each side:

- LexBFS-only: `1,2,3,4,5,u,v` (and 39 others),
- MCS-only: `1,2,3,4,5,v,u` (and 39 others).

This is consistent with Corneil-Krueger (2008): MCS and LexBFS are both
restrictions of maximal neighborhood search, and their ordering families are
neither nested nor disjoint.

## 2. Dynamic / locality result (NOT FOUND)

The formalization's locality theorem: after a single edge insertion/deletion,
the first position whose choice can change lies in the window between the two
endpoints (for a deletion, only the later endpoint can break); a suffix
regreedy from that position restores the canonical MCS ordering, so positions
past the window may also change.

- **Nearest published work:** Banerjee, Raman, Satti, *Maintaining Chordal
  Graphs Dynamically: Improved Upper and Lower Bounds,* CSR 2018, LNCS
  10846:29-40, Springer, 2018. That work maintains a perfect elimination
  ordering of a chordal graph under **deletion only** (decremental), with a
  different window notion (move common-neighbours before `u` to just after `u`).
  It is not the same statement as our insertion+deletion MCS-ordering locality.
- **Nearest fully-dynamic work (VERIFIED):** L. Ibarra, *Fully Dynamic
  Algorithms for Chordal Graphs,* SODA 1999, pp. 923-924; journal version
  *Fully Dynamic Algorithms for Chordal Graphs and Split Graphs,* ACM Trans.
  Algorithms 4(4):40, 2008, doi:10.1145/1383369.1383371. Supports both edge
  insertions and deletions, but maintains a clique-tree representation of a
  chordal graph (queries whether an update preserves chordality), not an MCS
  ordering of an arbitrary graph. Adjacent, not the same result.
- **Verdict:** the specific insertion+deletion MCS-ordering locality statement
  is **NOT FOUND** in the searched literature. It sits just below the folklore
  threshold: a specialist could plausibly derive it, but no published statement
  was located. `formalization.yaml` says "we are not aware of a prior
  formalization", which is accurate.

There is no "Agrawal et al. CSR 2018" — an earlier draft mis-cited the CSR 2018
paper; the correct authors are Banerjee, Raman, Satti.

## 3. Stability-boundary result (NOT FOUND)

The novelty lever for the Palomar submission: the common-ordering theorem
(if, along every chosen set, each vertex's neighbour count in `G'` is at least
its count in `G` and at most one more, then `G` and `G'` share an MCS ordering
under arbitrary tie-breaking) plus the matching / single-flip corollaries and
certified counterexamples delimiting the stability boundary.

- **Nearest published work:** Brandstädt, Dragan, Nicolai, *LexBFS-orderings
  and powers of chordal graphs,* Discrete Math. 171(1-3):27-42, 1997,
  doi:10.1016/S0012-365X(96)00070-2. That result is about LexBFS common PEOs
  of graph powers and is **negative for MCS** — the paper states that even for
  trees MCS does not give a common PEO of powers — so it does not subsume our
  positive stability statement.
- Searched the VibeMathed catalog (741 entries via `vibemathed.com/api/dataset`)
  for matching-stability / star-plus-matching / common MCS ordering: **NOT
  FOUND**.
- **Verdict:** the proved matching-stability result (and the star /
  star-plus-matching boundary, which is only an experimentally supported
  conjecture, not a theorem) is **NOT FOUND**. This is the contribution that
  carries the submission's novelty, per the supervisor roadmap. No asymptotic
  separation is claimed: in the unit-cost model the worst-case update costs at
  most `n` (insertion) or `n + 1` (deletion) units, the same order as a full
  recomputation; the executable itself is a naive adjacency-list
  implementation, not a linear-time one.

## 4. Consequences for the submission

- The locality result is **not** presented as a headline novelty; it is a
  supporting lemma. Research weight is on the stability boundary (NOT FOUND),
  which the roadmap already designates as the novelty lever.
- The "superset of LexBFS" overclaim is removed; README now states incomparability
  on general and chordal graphs with an explicit chordal witness.
- arXiv preprint (P4) related-work section will cite Ibarra (1999/2008) and
  Banerjee-Raman-Satti (2018) as the nearest prior art to the locality result
  and Brandstädt-Dragan-Nicolai (1997) to the stability result, with the NOT
  FOUND status stated as
  "we are not aware of" rather than a priority claim.
