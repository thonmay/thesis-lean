---
agent: devin-local
session: flowery-nerve
created: 2026-09-23T17:05:43Z
---
# Dynamic MCS: Palomar resubmission → arXiv → VibeMathed

Fix every item of the 2026-09-23 Palomar automated review by changing the Lean (not the prose), add a machine-checked stability-boundary theorem as the research-interest upgrade, resubmit as a new Palomar submission, then post to arXiv, VibeMathed and social channels.

## 0. Inputs and decisions (settled)
- Palomar review: `thesis-lean/palomer-automated-review.txt` (codex:gpt-5.6-sol, 2026-09-23). Supervisor review: `~/Downloads/Verdict.md`.
- Resubmit through https://submit.palomar-registry.org/ as a **new submission, Palomar ID left blank**.
- Scope: Lean repairs, locality headlines, operational cost **plus** the stability boundary.
- Cost model: **unit-cost query model** (count legality checks and pick steps from the running executable code).
- Authorship: **you and your supervisor**; the supervisor is also the independent reviewer.
- Neither `thesis-lean` nor `ai-dynamic-graph-algorithms` contains prior stability work or a harness. It gets built from scratch here.

## 1. Findings that shape the plan

### 1a. Verdict.md's Lean criticisms: all confirmed in the code
- Complexity proofs are `omega` over size bounds (`ComplexityHeadlines.lean:99-168`).
- `exec_insert_valid` / `exec_delete_valid` certify recomputation (`Challenge.lean:484-512`). There is no executable dynamic update.
- `greedyPick` uses `Classical.choose` (`Challenge.lean:132`), although `exists_IsMCSNext` builds the witness explicitly.
- `deleteCost` charges a suffix scan; `deleteUpdate` does a single check.
- The lowest-index clause in `IsMCSNext` makes the MCS order unique.
- `AxiomAudit.lean` prints `DynamicMCS.*` names, not the comparator's `Challenge.*` names.
- `README.md` is still the GitHub template.

### 1b. Locality is mostly proved already (in `Formal_gen003c01_eea71821.lean`)
`legal_after_laterPos` (l.825), `legal_middle_delete` (l.926), `insert_break_iff` (l.1096), `deletionBreaks_true_iff` (l.1235). Still missing as named lemmas: `insert_legal_before_window` (steps ≤ earlierPos) and the two null-update equalities.

### 1c. Verdict Phase 2 claim corrected (exhaustive check, set-valued MCS)
| Update F | Is there always a common order? | Evidence |
|---|---|---|
| single flip | yes | 0 failures, n ≤ 6 |
| insert-only matching / delete-only matching | yes | 0 failures, n ≤ 6; proof sketch below |
| insert-only 2-edge path | yes | 0 failures, n ≤ 6 (so matching is not the boundary) |
| mixed matching | **no** | n=4: G={01,03,12}, F={01,23} |
| insert-only triangle | **no** | n=5: G={02,04,12,13}, F={23,24,34} |
The verdict's G={01,02}, F={03,13} is not a counterexample (`0,2,1,3,4` is valid for both graphs).

**Proof sketch (monotone, inflation ≤ 1).** For every chosen set S and every unchosen x, count_{G'}(x) − count_G(x) ∈ {0,1}. Let M = max count in G and M′ = max in G′, so M′ ∈ {M, M+1}.
- If M′ = M, every G-max vertex is G′-max.
- If M′ = M+1, a vertex reaching M+1 in G′ had M in G, so it is G-max.
So a pick legal in both graphs always exists, and a greedy argument gives a common order. Deletions: swap G and G′.
Why mixed updates fail: one vertex can deflate while another inflates, and the n=4 counterexample shows exactly that.

### 1d. Build environment
- `thesis-lean` pins `leanprover/lean4:v4.35.0-rc2` (the Palomar minimum). Only 4.33 and 4.34 are installed. `thesis-brainstormig/.lake` has mathlib for 4.34, and `thesis-lean/.lake` does not exist.
- Needed (writes about 5 GB; runs after plan approval): `elan toolchain install leanprover/lean4:v4.35.0-rc2`, then `lake exe cache get && lake build` in `thesis-lean`. The 96-core host remains the final gate.

## 2. Palomar review item → fix
| Review item | Fix (Lean-side, no disclosure-only branch) | Steps |
|---|---|---|
| 1 Originality / literature | Literature search; cite Tarjan–Yannakakis 1984 (SIAM J. Comput. 13(3):566–579) exactly; say "novelty unknown" wherever the search is inconclusive | P0 |
| 2 Review status | Already `author-verified`; change to supervisor as reviewer and state what they checked | P1.8 |
| 3 Probe beyond window | Scan stops at `laterPos`; equivalence with the old scan proved via `legal_after_laterPos` | P1.4 |
| 4 Surrogate cost | Instrumented executable updates; cost theorems about the real control flow (deletion probe = 1 check) | P1.5, P1.6 |
| 5 Research interest | Stability boundary theorems (positive and negative) + locality as headlines | P1.3, P2 |

## 3. Implementation steps

### P0: Literature and provenance (blocker for the yaml and the paper, not for the Lean work)
- Search: Rose–Tarjan–Lueker 1976; Tarjan–Yannakakis 1984; Berry–Blair–Heggernes–Peyton (MCS-M 2004); Corneil–Krueger 2008; Beisegel et al. (end-vertex problems); Ibarra 2008 (dynamic chordal); Berry–Sigayret–Spinrad; Mezzini; Agrawal et al. CSR 2018; dynamic LexBFS.
- Output: `thesis-lean/LITERATURE.md` with citations, what each covers, and a verdict on (a) whether locality is folklore and (b) whether a **pre-existing open question** exists (for VibeMathed).

### P1: Lean repair (`thesis-lean/`)
1. **Environment:** install toolchain 4.35.0-rc2, fetch the mathlib cache, get a baseline `lake build`.
2. **Decidability refactor (single commit):** give `UGraph` decidable adjacency (`[DecidableRel adj]` field or instance). Make `neigh` and `IsMCSNext` decidable. Update all `ThesisLean/*`, `Challenge.lean`, `Solution.lean`.
3. **Computable `greedyPick`** from `filter`/`min'`, with `greedyPick_isMCSNext`. `mcsLoop`, `greedySuffix`, `insertUpdate`, `deleteUpdate` become computable. Acceptance: `#eval initOrder` on a concrete graph.
4. **Tie-break split:** add `IsMCSNextAny` / `IsMCSOrderingAny` (no index clause), with lemmas `IsMCSNext → IsMCSNextAny` and `IsMCSOrdering → IsMCSOrderingAny`.
5. **Locality headlines** (new module `ThesisLean/Locality.lean`): `insert_legal_before_window`, `legal_after_laterPos`, `legal_middle_delete`, `insert_break_iff`, `delete_break_iff`, `insert_null_update` (no break → `insertUpdate G' order u v = order`), `delete_null_update`.
6. **Window-bounded probe:** `firstBreakWindow` scans `order.drop k0 |>.take (k1+1-k0)`. Prove `firstBreakWindow_eq_filtered` against the old definition. Remove the fidelity caveat.
7. **Executable dynamic updates** (`ThesisLean/ExecUpdate.lean`): `execInsertUpdate` / `execDeleteUpdate` over `Adj n`, reusing `bestPick`/`mcsStep` for the regreedy from position k.
   - Refinement theorems `exec_insert_update_refines` / `exec_delete_update_refines`: the output equals the abstract update mapped through `val`.
   - Rename the current theorems to `exec_recompute_valid`, `exec_insert_recompute_valid`, `exec_delete_recompute_valid`.
   - Tests: `#eval` agreement with `mcsOrder` of the flipped matrix over all graphs with n ≤ 5, plus a few kernel `decide` checks at n ≤ 4.
8. **Operational cost (unit-cost query model):** `execInsertUpdateC` / `execDeleteUpdateC : … → List ℕ × ℕ` count legality checks and pick steps along the real control flow. Prove `(·.1)` equals the uninstrumented function. Headlines:
   - `insert_probe_checks ≤ laterPos − earlierPos`
   - `delete_probe_checks = 1`
   - `insert_null_cost` / `delete_null_cost`: no break → cost = probe checks only
   - `regreedy_picks = n − k0` when breaking at k0
   - corollary `update_cost_le_n` (worst case, stated as a corollary)
   - Delete the old surrogate `insertCost`/`deleteCost` and "the constant 2 is not sacred".
9. **Housekeeping:**
   - `AxiomAudit.lean`: `import Solution` and `#print axioms` exactly the comparator list.
   - New `README.md`: result, theorem map, build commands, model/cost disclaimer.
   - Remove the stale "PLANNED THEOREM" comment in `Exec.lean`.
   - Delete the now-unused `ComplexityHeadlines` surrogate code (keep the space lemmas only if kept in the comparator).

### P2: Stability boundary (`ThesisLean/Stability.lean`)
1. `scripts/mcs_stability.py` (in `thesis-lean`): the reproducible harness for the §1c table (n ≤ 6), with a CLI flag for n and update class. It is the experimental record for the paper.
2. Pen-and-paper proof write-up (supervisor checks it) of `monotone_inflation_le_one_common_order`: if every S and unchosen x has count difference in {0,1}, then MCS_any(G) ∩ MCS_any(G′) ≠ ∅.
3. Lean:
   - `commonPick_exists` (the M/M′ case split above)
   - `common_order_of_inflation_le_one` (greedy loop, reusing the `mcsLoop` pattern)
   - corollaries `single_insert_common_order`, `single_delete_common_order`, `insert_matching_common_order`, `delete_matching_common_order`
4. Negative results by `decide` on concrete instances: `mixed_matching_no_common_order` (n=4), `triangle_insert_no_common_order` (n=5; if kernel `decide` is too slow, prove it by case analysis on the forced first picks).
5. Stated as an open conjecture (not claimed): the characterization of insert patterns H (P3 works, K3 fails; P4, K1,3, … unknown). This is VibeMathed fallback material.

### P3: Palomar resubmission
- Rewrite `Challenge.lean` (statements with `sorry`) and `Solution.lean` (proofs) for the new list; update `comparator.json`. About 20 names: correctness 5, locality 7, executable refinement 2 plus 3 renamed recompute theorems, cost 5, stability 6.
- `formalization.yaml`:
  - authors: you + supervisor
  - description and scope rewritten around locality + stability + verified executable
  - fidelity: only the true remaining divergences (unit-cost query model; adjacency-matrix executable)
  - sources: proper Tarjan–Yannakakis citation; provenance per P0
  - review: supervisor named, with what they checked
  - axioms list re-derived from `AxiomAudit` output
- Gates: local `lake build`, leanchecker (CI workflow), `lake env lean AxiomAudit.lean`, then run the `Palomar Preflight` workflow on the exact commit. Push only when you say so.
- Submit the commit at submit.palomar-registry.org with the ID blank. If the review raises either/or items again, fix the Lean.

### P4: arXiv preprint
- Title (draft): *Locality and stability of maximum cardinality search orderings under edge updates, with a machine-checked implementation.* cs.DS, cross-list math.CO.
- Contributions, in order: (1) insertion window / deletion single-point locality + null updates; (2) the stability boundary (monotone inflation ≤ 1 ⇒ common order; mixed or triangle ⇒ not); (3) verified executable with operational cost; (4) harness data.
- The introduction says explicitly that the worst case equals static O(n+m) recomputation.
- Include measured window and suffix sizes on random / sparse / chordal families (harness extension); drop any "o(n+m) in practice" claim that isn't backed by data.
- Links: Palomar record, repo commit, AI-use statement. The supervisor provides the arXiv endorsement if needed.

### P5: VibeMathed
- If P0 finds a pre-existing open question that P2 or the locality work answers: submit that with the arXiv + Palomar links.
- Otherwise: submit the stability boundary as posed-and-answered, honestly labelled, AI tier as disclosed, Lean-verified via Palomar. Expect low significance. Run it through the auditor skill first.

### P6: Dissemination (after P3–P5 are live)
LinkedIn / X thread, ResearchGate / Academia mirror of the arXiv PDF, Lean Zulip post. Wording copied from the abstract, with no claims beyond it.

## 4. Verification
- Every Lean step: `lake build` green, no `sorry` outside `Challenge.lean`, `AxiomAudit` shows only `propext`/`Quot.sound`/`Classical.choice`.
- Refinement: `#eval` agreement tests (n ≤ 5) + `decide` spot checks.
- Stability: harness reproduces the §1c table; the Lean counterexamples match the harness output.
- Submission: CI (build + leanchecker) and Palomar Preflight green on the submitted commit.

## 5. Risks
- The decidability refactor touches every file. Doing it first in one commit avoids a double rewrite.
- 4.34 → 4.35-rc2 mathlib API drift: the baseline build (P1.1) catches it before new work starts.
- `decide` on the n=5 counterexample may be slow in the kernel; fallback is a manual case proof.
- If P0 shows locality is folklore, the research-interest weight rests on the stability theorems, which is one more reason they are in scope.
- The research-interest gate is still a judgment call; the stability boundary is the strongest available lever.
