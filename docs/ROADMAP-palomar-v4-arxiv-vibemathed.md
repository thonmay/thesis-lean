---
agent: devin-local
session: flowery-nerve
created: 2026-09-23T17:05:43Z
---
# Roadmap: Palomar v4 resubmission → arXiv → VibeMathed (dynamic MCS)

Fix every item of the 2026-09-23 Palomar automated review by changing the Lean rather than the prose, add a machine-checked stability-boundary result as the research-interest upgrade, resubmit to Palomar as a new submission, then publish on arXiv and VibeMathed and announce it.

## 0. Inputs and settled decisions
- Palomar review: `thesis-lean/palomer-automated-review.txt` (codex:gpt-5.6-sol, 2026-09-23; stays untracked because it is private). Supervisor review: `~/Downloads/Verdict.md`.
- Resubmission: https://submit.palomar-registry.org/, as a **new submission with the Palomar ID blank** (this is v4).
- Scope: Lean repairs + locality headlines + operational cost + **stability boundary**.
- Cost model: **unit-cost query model** (count legality checks and pick steps along the real executable control flow).
- Authorship: **you + supervisor**; the supervisor is also the independent reviewer.
- No prior stability work or harness exists in `thesis-lean` or `ai-dynamic-graph-algorithms`. It is built here.
- Rule for every reviewer either/or: **fix the Lean; never resolve an item by disclosure alone.**
- **Supervisor sign-off (2026-09-23):** P0, P1 and P2 approved as planned. P3, P4 and P5 each need a **supervisor audit before anything is submitted publicly**: we finish our own validation, send an audit package, and wait for written sign-off.

## 1. Findings

### 1a. Verdict.md's Lean criticisms: all confirmed
| Defect | Location |
|---|---|
| Complexity proofs are `omega` over size bounds | `ThesisLean/ComplexityHeadlines.lean:99-168` |
| `exec_insert_valid`/`exec_delete_valid` certify recomputation; no executable dynamic update | `Challenge.lean:484-512`, `ThesisLean/ExecFlip.lean:315-365` |
| `greedyPick` = `Classical.choose`, though `exists_IsMCSNext` builds the witness | `Challenge.lean:86-135` |
| `deleteCost` charges a suffix scan; `deleteUpdate` does one check | `Challenge.lean:309-314` vs `243-247` |
| Lowest-index clause ⇒ the MCS order is unique | `IsMCSNext`, third conjunct |
| `AxiomAudit.lean` audits `DynamicMCS.*`, not the comparator's `Challenge.*` | `AxiomAudit.lean:16-21` |
| README is the GitHub template | `README.md` |

### 1b. Locality is mostly proved already (`ThesisLean/Formal_gen003c01_eea71821.lean`)
`legal_after_laterPos` (l.825), `legal_middle_delete` (l.926), `insert_break_iff` (l.1096), `deletionBreaks_true_iff` (l.1235). Missing as named lemmas: `insert_legal_before_window` (steps ≤ earlierPos) and the two null-update equalities.

### 1c. Code architecture every change must respect
- **Two parallel namespaces:**
  - `DynamicMCS` holds the real development: `Formal_gen001c01_3939115c.lean` (UGraph, IsMCSNext, greedyPick, mcsLoop) and `Formal_gen003c01_eea71821.lean` (updates, validity).
  - `Challenge` is restated verbatim in `Challenge.lean` and again in `ThesisLean/SolutionBridge.lean`. It connects to the real development by `toDyn` transport lemmas (`greedyPick_val`, `mcsLoop_eq`, `firstBreak_eq`, `insertCost_eq`, …, `SolutionBridge.lean:351-679`).
  - ⇒ Every definition change goes into **three places in lockstep**: DynamicMCS, `Challenge.lean`, and `SolutionBridge.lean`, plus its transport lemma.
- **Exec layer:**
  - `ThesisLean/Exec.lean` (bestPick/mcsStep/mcsOrder)
  - `McsInvariant.lean`: the invariant `McListInv` is proved only from the initial state `([], List.range n)`; `bestPick_IsMCSNext` at l.230
  - `CardBridge.lean`, `BridgeParts{A,B,C}.lean`, `BridgeAssembly.lean`: `mcsOrder_eq_greedySuffix`
  - `ExecFlip.lean`: `setEdge_*` and the `exec_*` theorems
- **Comparator constraints:**
  - `Challenge.lean` may import Mathlib only.
  - Every definition used in a headline statement must be restated there.
  - Allowed axioms are `propext`, `Quot.sound`, `Classical.choice` ⇒ **no `native_decide`** (it adds `Lean.ofReduceBool`).

### 1d. Stability experiments (set-valued MCS, any tie-break; exhaustive for n ≤ 6, random sampling at n = 7, 8)
| One-sided update F (insert-only or delete-only) | Is there always a common order? | Smallest witness |
|---|---|---|
| single edge; matching of any size | yes (exhaustive n ≤ 6) | – |
| star K1,3, K1,4; star + matching (P3+K2, P3+2K2, K1,3+K2) | no failure found (exhaustive n ≤ 6, sampled n = 7, 8) | – |
| K3 | **no** | n=5: G={02,04,12,13}, insert {23,24,34} |
| P4 | **no** | n=6: G={03,05,12,14,23}, insert {25,34,45} |
| C4 / K3+K2 / spider S(2,1,1) / P5 | **no** | n=6 / 6 / 7 / 7 |
| 2P3 | **no** | n=8 (deletion) |
| **mixed** matching (some inserted, some deleted) | **no** | n=4: G={01,03,12}, F={01,23} |

The verdict's G={01,02}, F={03,13} is not a counterexample (`0,2,1,3,4` is valid for both graphs).

**Conjecture (Star–Matching Stability).** For a one-sided update F, MCS(G) ∩ MCS(G △ F) ≠ ∅ for **every** host graph G **iff** F is a star plus a matching, i.e. at most one vertex has F-degree ≥ 2.
- Any F with two vertices of F-degree ≥ 2 contains K3, P4 or 2P3 as a subgraph (short case analysis on whether the two vertices are adjacent or share a neighbour).
- All three have counterexamples.

**Proved sketch (matching case, inflation ≤ 1).**
- Along any chosen set S, count_{G′}(x) − count_G(x) ∈ {0,1}. Let M and M′ be the maxima in G and G′; then M′ ∈ {M, M+1}.
- If M′ = M, every G-max vertex is G′-max.
- If M′ = M+1, a G′-max vertex had count M in G, so it is G-max.
- A common legal pick always exists ⇒ the greedy construction gives a common order. Deletions: swap G and G′.
- The star centre can inflate by more than 1, so the star case needs a non-local argument. That is open research.

### 1e. Build environment
- `thesis-lean` pins `leanprover/lean4:v4.35.0-rc2` (the Palomar minimum). Installed toolchains: 4.33 and 4.34.
- `thesis-brainstormig/.lake` has mathlib for 4.34; `thesis-lean/.lake` does not exist.
- Setup (about 5 GB, runs after approval): `elan toolchain install leanprover/lean4:v4.35.0-rc2`, then `lake exe cache get && lake build` in `thesis-lean`.
- The remote 96-core host plus the CI leanchecker are the final gate.

## 2. Palomar review item → fix
| # | Review item | Fix | Steps |
|---|---|---|---|
| 1 | Originality / literature | Literature search; exact Tarjan–Yannakakis citation; "novelty unknown" where the search is inconclusive; revise provenance | P0, P3.2 |
| 2 | Review status | Supervisor named as reviewer, with what they checked | P3.2 |
| 3 | Probe beyond window | Scan stops at `laterPos`; equivalence to the old scan proved | P1.5 |
| 4 | Surrogate cost | Instrumented executable updates; theorems follow the real control flow (deletion probe = 1 check) | P1.6, P1.7 |
| 5 | Research interest | Locality headlines + stability boundary (matching theorem, obstructions, conjecture/characterization) | P1.4, P2 |

## 3. Implementation steps (each step ends green: `lake build`, zero `sorry` outside `Challenge.lean`)

### P0: Literature and provenance (in parallel with P1; blocks P3.2 and P4)
- Sources:
  - Rose–Tarjan–Lueker 1976
  - Tarjan–Yannakakis 1984 (SIAM J. Comput. 13(3):566–579)
  - Berry–Blair–Heggernes–Peyton 2004 (MCS-M)
  - Corneil–Krueger 2008
  - Beisegel et al. (end-vertex problems of graph searches)
  - Ibarra 2008 (dynamic chordal)
  - Berry–Sigayret–Spinrad, Mezzini
  - Agrawal et al. CSR 2018
  - dynamic LexBFS / graph-search stability
- Output `docs/LITERATURE.md`: citations, what each covers, and verdicts on
  - (a) whether locality is folklore
  - (b) whether a **pre-existing open question** exists that locality or stability answers (the VibeMathed route)
  - (c) whether the star–matching phenomenon is known

### P1: Lean repair (`thesis-lean/`)
1. **Environment + baseline.** Install 4.35.0-rc2, fetch the cache, `lake build` the current HEAD, fix any API drift. Point lean-lsp at `thesis-lean`.
2. **Explicit `greedyPick`** in DynamicMCS, Challenge and SolutionBridge. Body: `(U.filter (neigh = U.sup neigh)).min' _` with `greedyPick_isMCSNext`.
   - Classical decidability of `adj` is kept. A full `DecidableRel` refactor clashes with `open Classical` everywhere and adds nothing once P1.6 gives a verified executable.
   - Acceptance: no `Classical.choose` in any update definition; `greedyPick_val` transport re-proved.
3. **Tie-break split.** Add `IsMCSNextAny` / `IsMCSOrderingAny` (no index clause), with lemmas `IsMCSNext.toAny` and `IsMCSOrdering.toAny`.
4. **Locality module** `ThesisLean/Locality.lean`:
   - `insert_legal_before_window` (new)
   - re-export `legal_after_laterPos`, `legal_middle_delete`, `insert_break_iff`, `delete_break_iff`
   - `insert_null_update`: `firstBreakWindow … = none → insertUpdate G' order u v = order`
   - `delete_null_update`: the same for `deleteUpdate` (both via `greedySuffix_full`)
5. **Window-bounded probe.** Redefine `firstBreakWindow H order k0 k1 := firstBreakAux H order k0 ((order.drop k0).take (k1 + 1 - k0))`.
   - Prove `firstBreakWindow_eq_filtered` (equals the old full-scan-then-filter) using `legal_after_laterPos`.
   - Re-prove `insert_update_valid`.
6. **Executable dynamic updates** `ThesisLean/ExecUpdate.lean`:
   - `execLegal a chosen w : Bool` (via `cardC`), with `execLegal_iff : execLegal … = true ↔ IsMCSNext (toUGraph a …) …`
   - `execFirstBreakWindow`, `execRegreedyFrom a pref`, `execInsertUpdate`, `execDeleteUpdate`
   - **Generalize `McListInv`/`foldl_mcsStep` from `([], range n)` to an arbitrary valid prefix state `(pref.reverse, range n \ pref)`.** This is the main new bridge proof.
   - Refinement: `exec_insert_update_refines` / `exec_delete_update_refines`: the output = `(insertUpdate G' ord u v).map val` for `ord` with `ord.map val = order`.
   - Rename `exec_insert_valid` → `exec_insert_recompute_valid`, `exec_delete_valid` → `exec_delete_recompute_valid`, and add `exec_recompute_valid` (from `mcsOrder_eq_greedySuffix`).
   - Tests: `#eval` agreement against `mcsOrder` of the flipped matrix for all graphs with n ≤ 5; kernel `decide` spot checks at n ≤ 4 (no `native_decide`).
7. **Operational cost (unit-cost query model)** `ThesisLean/ExecCost.lean`:
   - `execInsertUpdateC` / `execDeleteUpdateC : … → List ℕ × ℕ` count `execLegal` calls and `bestPick` steps; `(·.1)` equals the plain function.
   - Headlines: `insert_probe_checks_le_window` (≤ laterPos − earlierPos), `delete_probe_checks_eq_one`, `insert_null_cost` / `delete_null_cost` (no break ⇒ cost = probe only), `regreedy_picks_eq` (= n − k0), and the corollary `update_cost_le_n`.
   - Delete the surrogate `insertCost`/`deleteCost`/`mSuffix`/`edgeCount` and the "constant 2" note. `mcsOrder_length`/`adj_space_bound` stay internal, not in the comparator.
8. **Housekeeping:**
   - `AxiomAudit.lean` → `import Solution` and `#print axioms` for exactly the `comparator.json` list; add it as a CI step in `.github/workflows/lean_action_ci.yml`.
   - New `README.md`: result, theorem map, model and cost statement, build/verify commands.
   - Delete the stale "PLANNED THEOREM" block in `Exec.lean` and the `ExecBridge.lean` header text.
9. **Optional, last, only if everything is green:** rename the hash-named modules (`Formal_gen001c01_3939115c` → `Core`, `Formal_gen003c01_eea71821` → `Update`) for readability in the paper.

### P2: Stability boundary
1. **Harness** `thesis-lean/scripts/mcs_stability.py`: standard library only, fixed seed, CLI `--n --pattern --mode {ins,del,mixed} --sample`. It regenerates the §1d table into `docs/stability-data.md`.
2. **Paper proofs** (supervisor checks them before the Lean work):
   - (a) the inflation ≤ 1 theorem (§1d sketch)
   - (b) the K3 / P4 / 2P3 obstructions and the "two high-degree vertices ⇒ contains one of them" lemma
   - (c) the star case: research target, time-boxed
3. **Lean** `ThesisLean/Stability.lean`, stated on `IsMCSOrderingAny`:
   - Core: `common_order_of_inflation_le_one`. Hypothesis: `∀ S x, G.neigh S x ≤ G'.neigh S x ∧ G'.neigh S x ≤ G.neigh S x + 1`. Conclusion: `∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord`. Proof by `commonPick_exists` plus the `mcsLoop` pattern.
   - Update model: F as a `UGraph n`, `IsMatching F` (every vertex has ≤ 1 F-neighbour), `insertEdges G F` (sup, with `Disjoint`) and `deleteEdges`.
   - Corollaries: `single_insert_common_order`, `single_delete_common_order`, `insert_matching_common_order`, `delete_matching_common_order`.
   - Negatives by `decide` on concrete `Fin 4/5/6` instances: `mixed_matching_no_common_order`, `triangle_no_common_order`, `p4_no_common_order`. Fallback if the kernel is too slow: a manual case split on forced first picks.
4. **Outcome options for the paper:**
   - (A) full characterization proved: the star case plus a lifting argument for supergraphs of the obstructions
   - (B) matching theorem + obstructions + a precisely stated conjecture with data
   - B is the guaranteed floor; A is the stretch goal.

### P3: Palomar v4 resubmission
1. `Challenge.lean` restates every new definition (Mathlib-only). Theorem statements get `sorry`. `Solution.lean` proves them through the SolutionBridge transport. `comparator.json` gets the new list, about 22 names:
   - correctness: `init_valid`, `insert_update_valid`, `delete_update_valid`, `update_from_prefix`, `greedySuffix_full`
   - locality: 7
   - exec: 2 refinement + 3 recompute
   - cost: 5
   - stability: core + 4 corollaries + 3 counterexamples
2. `formalization.yaml`:
   - authors: you + supervisor
   - description/scope rewritten (locality + stability + verified executable; worst case = static recomputation)
   - fidelity: only the true divergences (unit-cost query model; adjacency-matrix executable; canonical vs set-valued MCS explained)
   - sources: exact Tarjan–Yannakakis citation; provenance per P0
   - review: supervisor + what they checked
   - **automation: add this session's tooling (Devin agent + model)** next to the DeepSeek harness
   - axioms taken from the `AxiomAudit` output
3. Gates: local `lake build`, CI build + leanchecker + AxiomAudit, then the **Palomar Preflight** workflow on the exact commit. Push only when you say so.
4. **Gate A (supervisor audit).** Send audit package A (§3a). Do not submit until the supervisor signs off in writing. Fix any findings, re-run the gates, re-send if the commit changed.
5. Submit the audited commit (exact hash) with the ID blank.
   - After the new submission is accepted into review, withdraw the old v3 submission (your action; irreversible).
   - If it passes: decide on "Register this result" (makes the record, repo and commit public).

### P4: arXiv preprint (after Palomar passes)
- Title: *Locality and stability of maximum cardinality search orderings under edge updates, with a machine-checked implementation.* Primary cs.DS, cross-list math.CO. License CC BY 4.0.
- Contributions:
  1. locality (insertion window, deletion single point, null updates)
  2. stability boundary (the matching theorem; the K3/P4/2P3 obstructions; the star–matching conjecture or characterization)
  3. verified executable + operational cost
  4. experimental data
- The introduction states that the worst case equals static O(n+m) recomputation.
- Empirical section: window and suffix sizes on random / sparse / chordal families (harness extension, Python mirror cross-checked against Lean `#eval`). Any "typically small" claim is backed by this data or dropped.
- Code and data availability: repo commit, Palomar record, AI-use statement. The supervisor provides the arXiv endorsement.
- **Gate B (supervisor audit).** Send audit package B (§3a). Upload to arXiv only after written sign-off on the exact PDF and source.

### P5: VibeMathed
- **Route 1 (preferred):** a pre-existing open question from P0 that is answered in the preprint.
- **Route 2 (fallback):** the stability question, disclosed as posed-and-answered, AI tier as disclosed, Lean-verified via Palomar; expect low significance. If only outcome B is reached, submit it as "partial".
- Run it through the auditor skill first.
- **Gate C (supervisor audit).** Send audit package C (§3a). Submit only after written sign-off.

### P6: Thesis and dissemination
- Update the ELTE thesis chapter to the new theorem set (tie-break split, locality, stability) so the thesis, Palomar and arXiv agree.
- After P3–P5 are live and audited: LinkedIn/X thread, ResearchGate/Academia mirror of the arXiv PDF, Lean Zulip post. Wording copied from the abstract.

### 3a. Supervisor audit packages (our own validation first, then send)
| Gate | Before | Package contents (all tied to one exact commit hash) |
|---|---|---|
| A | Palomar submit (P3.5) | commit hash; green CI run (build + leanchecker + AxiomAudit) and Palomar Preflight links; `AxiomAudit` output; comparator list with a one-line informal reading of each statement; `Challenge.lean`↔`SolutionBridge.lean` definition-diff check; `formalization.yaml` diff vs v3 with a mapping to review items 1–5; `docs/LITERATURE.md`; `docs/stability-data.md` + harness command |
| B | arXiv upload (P4) | PDF + LaTeX source; claim-by-claim table (paper claim → Lean theorem name or "paper proof / conjecture"); Palomar record link; harness data; AI-use statement; author list |
| C | VibeMathed submit (P5) | draft entry text (question, source, earliest reference, status, AI tier, verification rung); auditor-skill report; links to arXiv and Palomar |

Own validation before sending any package: every gate in §4 green on that exact commit/PDF, with no unresolved TODOs. Record each sign-off in `docs/audit-log.md` (date, gate, commit/PDF hash, findings, resolution).

## 4. Verification
- Lean, every step: `lake build`; no `sorry`/`admit`/`native_decide` outside `Challenge.lean`; `lake env lean AxiomAudit.lean` shows only the permitted axioms.
- Refinement: `#eval` agreement for n ≤ 5, `decide` spot checks for n ≤ 4.
- Stability: the harness reproduces the §1d table; the Lean counterexample instances equal the harness witnesses.
- Submission: CI and Palomar Preflight green on the exact submitted commit; `Challenge.lean` definitions verbatim-identical to those in `SolutionBridge.lean`.

## 5. Dependency order and exit criteria
P1.1 → P1.2 → P1.3 → (P1.4, P1.5) → P1.6 → P1.7 → P1.8 → P2.3 → P3. P0 and P2.1–2.2 run in parallel with P1.
- Exit P1: all review items 3 and 4 fixed in Lean.
- Exit P2: floor outcome B done.
- Exit P3: Gate A signed off, then Palomar passes.
- P4 (Gate B) → P5 (Gate C) → P6 follow in that order; no public step without the matching sign-off.

## 6. Risks
- Lockstep edits across three namespace copies: mitigated by changing one definition at a time and re-proving its transport lemma immediately.
- The prefix-generalized exec invariant (P1.6) is the largest new proof; the bridge files already contain the step lemmas it needs.
- 4.34 → 4.35-rc2 API drift: caught at the P1.1 baseline.
- Kernel `decide` on n = 5/6 instances may be slow: manual case-split fallback.
- The star case (P2.2c) may not yield to a proof: outcome B is still a coherent paper.
- If P0 finds locality is folklore, the research weight moves to stability, which is already in scope.
- The research-interest gate is still a judgment call; the stability boundary is the strongest lever available.
