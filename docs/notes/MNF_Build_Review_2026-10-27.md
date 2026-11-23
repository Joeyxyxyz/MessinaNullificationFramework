# MNF project inventory — cross-check for tonight's build

Reviewer: Claude (Fable 5.1), 2026-10-27. Everything below that says *compiled* or *kernel-checked* was
run here, in this session, on the stated toolchain; nothing is taken from a file's own header.

## 0. Verdicts in one screen

| | Verdict | Evidence |
|---|---|---|
| **Bundle 1** — `mnf_qexp_v0_1` core (7 files) | **GO** | Rebuilt here as a lake project with Lean **4.28.0** (release build, no Mathlib): 0 errors, 0 warnings. Kernel audit of every `MNF.*` theorem: only `propext`, `Classical.choice`, `Quot.sound`; **0 `sorryAx`, 0 `ofReduceBool`**. Matches `AXIOM_AUDIT_core.md`. The missing `lakefile.lean`, `lean-toolchain`, root module and `Audit.lean` are in `bundle1_mnf_core/`. |
| **Bundle 2** — Sturm–Liouville | **GO, with the consolidated file only** | None of the three corpus SL files is clean as-is (§2). The consolidated `SturmLiouville/SimpleEigenvalues.lean` compiles at the corpus pin (Lean **4.24.0 / Mathlib f897ebcf**) in 90 s; `sturm_liouville_simple_eigenvalues` and its whole chain are kernel-checked on the standard three axioms. This is the **first kernel verification of the capstone** — the master file's own header says "pending kernel verification pass". |
| **Bundle 2** — signed multiplicity | **GO as a conditional theorem; NO-GO as "resolution"** | `signed_multiplicity_resolution` (output71/79) is kernel-checkable but its hypothesis `SpeiserStrengthened` *is* "RH → all zeros simple". Two of its three "mechanisms" are vacuous (§3). The honest form is `MNF.RH.allZerosSimple_of_rh_of_line` in the consolidated library. |
| **Bundle 2** — 0.0e / topological (Batch16, 17.1) | **GO after one fix** | Batch17_1: clean (record arithmetic). Batch16 has **two `sorry`** (`riemannZeta (-2) = 0`, `riemannZeta (-4) = 0`); Mathlib closes both with `riemannZeta_neg_two_mul_nat_add_one`. Everything else in it is `decide`/`simp` on finite types. |
| Two-axiom interface (SpectralGap + HPContext) | **No file holds it** | There is no `HPContext.lean` / `SpectralGap.lean` in the project. The gap axiom appears as a hypothesis in output40/71/72/79/83/86; "HPContext" appears only in prose. The nearest formal objects are output86's `PoleProbeContext` (carries the false axiom `func_eq_deriv` and a `sorry`) and stub 2's `HilbertPolyaOperator` (a `Classical.choice` placeholder eigenfunction). Use `MNF.RH.SpectralGapHyp` and `MNF.RH.rh_of_symmetric_operator` (§4). |

## 1. Bundle 1 — `claude/mnf_qexp_v0_1/`

- All seven files rebuilt from the project copies (`MNFCore_X.lean` → `MNFCore/X.lean`), import order
  Operator, Bits → WState, GHZ → Hadamard; Decay, Conservation. `lake build`: 10 jobs, clean.
- Axiom audit (`lake env lean Audit.lean`, custom `#audit_all` that walks every `MNF.*` theorem the
  kernel knows, 154 entries incl. auto-generated ones): no theorem depends on anything but the
  standard three. The 153 named theorems of `AXIOM_AUDIT_core.md` are all present.
- `w_x_single_6` / `w_x_nbody_6` use `decide` with `maxRecDepth 200000`; they are kernel
  evaluations, not `native_decide` — fine.
- **Gap confirmed:** the Mathlib layer `MNFQ/{Dictionary,Decay,Ladder}.lean` is referenced in the
  docstrings of Decay, Conservation and Hadamard (`MNFQ.Decay.one_crossing_unique`,
  `MNFQ.Dictionary`, `MNFQ.Ladder`) and is **not in the project under any name**. The core layer does
  not import it, so Bundle 1 builds without it; the three claims that live there (t* = T1 ln 2,
  α = 1/2 ⟺ r² = 1/2, ⟨X_k⟩_W = 0 for general n) stay **[VERIFIED numerically]**, not [PROVED], until
  the layer is re-authored. Say so in the README.

## 2. Bundle 2 — Sturm–Liouville: which file is canonical

Reading all three (plus the two reports) gives this lineage:

| file | what it is |
|---|---|
| `sturm_liouville_master.lean.txt` | Joey's hand-patched master (fixes 1–4 close `exact?`/`skip` in the aux lemma, one with `grind`). **No `IsSimpleEigenvalue`, no capstone** in the body despite the header. Never kernel-verified ("pending"). |
| `Strum_LouiMasterArist.lean.txt` | Aristotle's return on the master (request `5d1f21f9`). Report: capstone missing; `eventually_nonzero_of_confining_eigenfunction_aux` hit a type error; `_fixed` variants "already declared". Body contains `exact?` and `skip`. |
| `sturm_liouville_PHASE1_COMPLETE.lean` | = the Aristotle return above **plus a hand-appended §15** (`IsSimpleEigenvalue`, capstone via `wronskian_zero_of_l2_final`). Still contains the `exact?`/`skip` aux lemma. |
| `sturm_liouville_PHASE1_COMPLETE-1.lean.txt` | Duplicate download (browser `-1` suffix); not re-read. |
| `strum_louifinal.lean.txt` | Second Aristotle run (`83f88ece`). Report says the aux lemma was **sorry'd** to let the rest verify; the capstone was verified under the alternate name `_proven`. Body still has `exact?` in the aux lemma. |

Every proof the capstone actually needs is **identical, character for character, across the three
files**; what differs is the broken/duplicated aux chain and whether the capstone is present. The
consolidated file keeps exactly the 14 lemmas on the dependency path (capstone →
`wronskian_zero_of_l2` → `tendsto_zero_and_deriv_zero_of_eigenfunction` → …), drops
`…_aux` and its copies `_v2…_v9`, `…_final`, `…_fixed`, `…_fixed_v2`, `…_proven`, and replaces
`import Mathlib` with the seven modules used. Compiled: 0 errors; 7 linter warnings (unused simp
args, one deprecation), nothing semantic. sha256 `e5ffa01d168f8ffad648f32b0b2daaca1e29d3f85677bbee0cfe9f8c43b40354`.

**Canonical: `bundle2_afm_core/SturmLiouville/SimpleEigenvalues.lean`.** Retire the five corpus
files to an `archive/` folder; cite them as provenance (Aristotle request ids above).

What the theorem says, so the paper matches it: for `V : ℝ → ℝ` continuous with `V → +∞` at both
ends (`IsConfiningPotential`), any two `C²`, `L²`, nonzero solutions of `−u'' + V u = λ u` on all of
ℝ are proportional. That is the simplicity of the point spectrum of a 1-D Schrödinger operator with
confining potential — a classical fact, now in Lean. It says nothing about ζ by itself (§4).

## 3. Bundle 2 — signed multiplicity: which file, and what it proves

| file | status |
|---|---|
| `output57_signed_multiplicity.lean` | Comes back from the project **mojibake-encoded** (UTF-8 read as Latin-1); unusable as stored. `output57.lean.txt` is the readable copy. |
| `output56_*` (3 files + 2 txt) | Earlier Path-D drafts; superseded. |
| `output71_signed_resolution.lean` | Merge of 56+57: `SignedNullClass`, three "mechanisms", capstone `signed_multiplicity_resolution`. |
| `output71_minimal_axiom.lean` | The gap/Bridge/MultiplicityBoundOne version (defs the library inherits). |
| `output72_master_theorem.lean` | Four-path master theorem. |
| `output79_definitive_capstone.lean` | The same signed capstone with provenance notes. **Canonical among the corpus files.** |

What `signed_multiplicity_resolution` establishes, read literally:

- hypotheses: `SpectralGapProperty S (1/2)`, `SpeiserStrengthened`, `OrderCharacterization`;
- `SpeiserStrengthened` is *defined* as `RiemannHypothesis → DerivativeNonvanishing`, i.e. **RH ⟹ every
  nontrivial zero is simple**. That is not Speiser's theorem (which concerns ζ′ off the line) — it is the
  simple-zeros conjecture under RH, assumed;
- mechanisms 1 and 2 (`neg_reservoir_killed`, `pos_reservoir_killed`) hold because the multiplicity
  deviation is an integer ≥ 0 classified at Δ = 1: those classes are empty by construction (this is
  the "SimpleBound is redundant" finding in `learnings-and-principles.md`, seen from the other side);
- `OrderCharacterization` is a theorem (`MNF.RH.order_one_iff_deriv`), not a hypothesis.

So the capstone is `gap(=RH) ∧ (RH → simple) ⟹ simple`. It is fine as a kernel-checked **conditional**
statement; it must not be deposited as a resolution. The consolidated library states it without the
costume: `allZerosSimple_of_rh_of_line (hRH) (hline : ζ′ ≠ 0 at zeros on the line) : AllZerosSimple`,
and records in `DEPOSIT_MAP.md` that `AllZerosSimple` is open.

Also: output71's `zeta_order_ge_one` cites `riemannZeta_two`, which lives in
`Mathlib.NumberTheory.LSeries.HurwitzZetaValues` — fine under `import Mathlib`, breaks under narrowed
imports. The library's proof avoids it (anchored at `riemannZeta_zero` on the convex half-plane).

## 4. The two-axiom interface and the six AXLE theorems

| AXLE id | theorem | where it lives now |
|---|---|---|
| `22abc227` `master_enforcement` | gap on `Set.range (N Δ)` | operator core (ℕ), Vol 1 — Bundle 1's `MNF.N`/`classify` family reproves the same facts |
| `572b70d1` `shifted_bounded` | \|x\| < 1/2 on S | `MNF.RH.shifted_bounded` (Core.lean) |
| `c133ead0` `tau_half_real` | gap + bound ⟹ S ⊆ {0} | `MNF.RH.tau_threshold` (Gap.lean) |
| `3de41f1f` `functional_equation_balance` | probe balance N + S = 0 | definitional; `sign_gate_trivial` records that it is content-free on a symmetric set |
| `f854b8e9` `leveling_theorem` | gap(1/2) ⟹ probes read 0 ⟹ on line | `MNF.RH.riemannHypothesis_iff_gap_half` — now **unconditional and an equivalence** |
| `01ae8bf9` `resolution_from_two_axioms` | gap + Bridge ⟹ RH | Bridge is **proved** (`riemannHypothesis_iff_strip`); one axiom left, and it is RH |

The interface the AFM v7 text describes — "SpectralGap + HPContext" — formalizes as:

- `MNF.RH.SpectralGapHyp Δ` (Hypotheses.lean). Kernel-checked facts about it: equivalent to RH for every
  Δ ≥ 1/2 unconditionally and for every Δ > 3/8 given the 7/8 theorem; insufficient for every Δ ≤ 3/8.
- `MNF.RH.rh_of_symmetric_operator`: a symmetric operator on a complex inner-product space whose
  eigenvalues include (ρ − 1/2)/i for every nontrivial zero gives RH, in one step. That is the whole
  of the HPContext → RH implication; the content is entirely in constructing the operator.
- The SL theorem of §2 connects to this only through a Hilbert–Pólya operator *that is a 1-D
  Schrödinger operator with confining potential*; no file constructs one. The two corpus bridges are
  vacuous as written (`sl_simplicity_implies_multiplicity_bound` ends in `→ True`;
  `HilbertPolyaOperator.spectral_match` quantifies a `Classical.choice ⟨fun _ => 0⟩` eigenfunction).

All 40 statements of the consolidated library were Comparator-accepted on the laptop today
(`qrh-mnf-receipt.tar.gz`); the 34 Mathlib-only ones also compile at the corpus pin and are in
`bundle2_afm_core/`.

## 5. Dependency graph and build order (Bundle 2)

```
SturmLiouville/SimpleEigenvalues.lean     — Mathlib only (7 modules); no MNF import
MNF/RH/Core.lean                           — Mathlib only
MNF/RH/Gap.lean                            — imports Core
MNF/RH/Hypotheses.lean                     — imports Gap (+ InnerProductSpace.Spectrum)
Audit.lean                                 — imports both; 39 #print axioms, 39 #check
```
No corpus file imports another (every one is `import Mathlib` + redefinitions), so output72 does
**not** import output71 etc.; the "chain" in the headers is textual. The lakefile pins Mathlib
`f897ebcf`; on the ThinkPad: `lake update && lake exe cache get && lake build && lake env lean Audit.lean`.
Expect the cache fetch to dominate (the proof files build in ~2 min).

## 6. Duplicates and `.lean.txt` (spot-checked)

- `*-1.lean.txt`, `* (1).lean.txt`: browser re-download suffixes; treat as duplicates (the excerpts of
  `output83_speiser_double_zero` and its `-1` that came back from search are identical; not diffed byte for byte).
- `output.lean (N).txt`: the ones opened here ((12), (14), (15), (71)) are mojibake-encoded Aristotle
  outputs (same encoding fault as output57); the readable content is in the named `outputNN_*.lean`
  files where those exist.
- Rule holds: prefer `.lean`; `.lean.txt` is the archive copy — **except** the SL set, where the
  `.lean` (PHASE1_COMPLETE) is the one with the appended capstone and the `.txt` files carry the
  reports.

## 7. OUT list — nothing on it needs to come IN tonight

- Yang–Mills Lagrangian: separate paper, not AFM.
- Batch1–14 / MdBatch / `_aristotle`: operator core and YM (Vol 1); they do not feed the SL theorem
  (which imports nothing from them).
- The only OUT items the AFM text leans on are the operator identities (`master_enforcement`), and
  Bundle 1 reproves those on ℕ and ℚ.

## 8. Risk list (register discipline)

| file | problem | action |
|---|---|---|
| Batch16_ZeroZeroE_Field | 2 × `sorry` (trivial zeros of ζ) | close with `riemannZeta_neg_two_mul_nat_add_one` |
| output86_pole_probe | `axiom func_eq_deriv` (false as stated) + `sorry` in `rh_and_speiser_implies_simple` | withdrawn; replaced by `deriv_reflect` |
| output83 | `axiom argument_principle_double_zero_forces_left_strip_zero` (would make RH ⟹ simple zeros a theorem) | withdrawn (DEPOSIT_MAP §5) |
| output45 | `axiom speiser_theorem` | keep as named hypothesis `SpeiserTheorem` |
| output71/79 | `SpeiserStrengthened` = RH → simple, named as if Speiser's | relabel (§3) |
| aristotle_stress_test_synthesis | `sl_simplicity_implies_multiplicity_bound : … → True` | vacuous; do not deposit |
| aristotle_stub_2 | `HilbertPolyaOperator` over `Classical.choice ⟨fun _ => 0⟩` | vacuous; do not deposit |
| output40, output66–70 | `N_count`, `pair_corr_stat := Classical.choice …` | not about ζ; do not deposit |
| output.lean (71).txt and other `.txt` Aristotle returns | `exact?` left in proofs | archive only |
| output.lean (95qi) | `native_decide` (`vacuum_pool_accumulation`) | out of scope tonight; note for Vol 3 |
| Bundle 1 | none found | — |

## 9. What is in the tarball

```
MNF_Build_Review.md                      this document
bundle1_mnf_core/                        Lean 4.28.0, no deps; `lake build && lake env lean Audit.lean`
  lakefile.lean  lean-toolchain  MNFCore.lean  MNFCore/{Operator,Bits,WState,GHZ,Hadamard,Decay,Conservation}.lean  Audit.lean
bundle2_afm_core/                        Lean 4.24.0 / Mathlib f897ebcf
  lakefile.lean  lean-toolchain  SturmLiouville.lean  SturmLiouville/SimpleEigenvalues.lean
  MNF.lean  MNF/RH/{Core,Gap,Hypotheses}.lean  Audit.lean
```
Both audits were run here; the expected output of each is that every line reads
`depends on axioms: [propext, Classical.choice, Quot.sound]` (Bundle 1 lines may list fewer).
