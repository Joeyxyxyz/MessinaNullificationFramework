# MNF formal corpus map — every operation beyond the projector N

Written 2026-11-01 for the "formal corpus map" angle of Joey's request *"explore beyond projection operations with the Nullification framework. explore Injection & ejection. and much more."*

**Method.** Read (not compiled — there is no Lean toolchain on this machine) the 301 files in
`C:/Users/jmess/Downloads/nullification_cascade_lean/files/`, plus `MNF_Bridge78.lean`, `mnf_wormhole_nsa_merged.lean` (byte-identical to the corpus copy),
the two PDFs (via `pdftotext`), the docx (via zipfile), the compilation md, the OTOC map, the Oct-24 inventory, the four solver `.py` files and the
quimb notebook. Every Lean quote below is verbatim from the file named. Proof status is read off the source:

| label | meaning |
|---|---|
| **proved** | a complete tactic/term proof is present in the file. I cannot run the kernel, so "proved" means *a proof text is there and nothing in it is a placeholder*. Where Aristotle's header says "The following was proved by Aristotle" I say so. |
| **sorry** | the theorem body is `sorry` (or a tuple containing `sorry`). |
| **axiom** | declared with `axiom`. |
| **True-stub** | a `def … : Prop := True` or a structure whose fields are all `True`, discharged by `trivial`. |
| **def-only** | a definition with `#eval` demonstrations and no theorem about it. |
| **exact?** | the proof ends in the search tactic `exact?`; it compiles only if the search succeeds in that environment (Aristotle recorded one such stall). |
| **negated** | Aristotle proved the *negation* of the statement as written. |

Register for claims: **(a)** what the corpus defines/proves, **(b)** what I propose, **(c)** what the OTOC data showed (pointers to `inventory.md` / `STATUS.md`; nothing redone here).

Sorry counts: `grep -c sorry` gives 352 lines in 73 files, but that counts prose ("Do not add sorry", "Zero sorry"). A proof-position regex gives ≈243; where it matters I counted by hand (§5).

Revision 2026-11-03 (the first pass was cut off before it reported): every quoted definition, the §5 sorry counts and the negative (absence) claims were re-checked against the files by grep; stale section cross-references were repaired; §1.4 and §1.20 were refined with two grep hits the first pass missed (both turn out to be non-N content).

---

## 0. The three-line core, and the first thing to know about it

```lean
-- Nullification_Core.lean (namespace Nullification, ℝ, Mathlib)
def nullify (Δ : ℝ) (x : ℝ) : ℝ := if |x| ≥ Δ then x else 0
def remainder (Δ : ℝ) (x : ℝ) : ℝ := x - nullify Δ x
def classify (Δ : ℝ) (x : ℝ) : NullClass :=
  if x = 0 then NullClass.zero
  else if |x| ≥ Δ then NullClass.observable
  else NullClass.nullified
```

The corpus contains **~100 re-declarations** of this operator under the names `N`, `nullify`, `N_int`, `N_nlos`, `nullify_nat`, `nullifyR`, `N_nat`, `nullifyNorm`, `nullifyBloch`, `nullifyComponentwise`, in six carrier types, and the three-class enum is re-invented at least ten times (`NullClass` with constructors `zero/observable/nullified`, or `ground/reservoir/observable`, or `Vacuum/Reservoir/Observable`; `EnergyClass` `zero/reservoir/observable` or `zero/subthreshold/observable` or `quantified/infinitesimal/undefined`; `EntropyClass`; `ValueClass`; `State`; `NullSphere center/surface/exterior`; `QuantumClass`; `HyperType`; `FluorideClass`). Every file is self-contained; nothing imports anything except two files that import non-existent modules (§4.8). The operations catalogued below are therefore **operations on one scalar threshold map**, re-proved per file.

Definition census (grep over all 301 files):

| form | files | note |
|---|---|---|
| `if x >= Δ then x else 0` on `Nat`/`ℕ` | 57 | one-sided; the Batch 1–17 "core library" |
| `if \|x\| ≥ Δ then x else 0` on `ℝ` (or `ℤ`) | 40 | two-sided; everything from output56 on, wormhole, Core |
| `if E < Δ then 0 else E` / `if x ≥ Δ then x else 0` on `ℝ` **without** absolute value | 3 | `MdBatch2.lean:50`, `MdBatch4.lean`, `MdBatch7.lean:97` — a one-sided real operator, inconsistent with Core for x < 0 |
| `def N (Δ E : ℝ) : ℝ := E` | 1 | `MdBatch1.lean:55` — N is the **identity** in that file (Wightman-axiom batch; its "nullification" theorems are vacuous) |
| `nullifyR (Δ x : Float)` | ~6 | Float, `#eval` only |
| `nullifyNorm (Δsq : Nat) (v : Vec2)`, `nullifyNorm3`, `nullifyBloch (Δsq) (r : BlochVec)` | 3 | norm-based, threshold on \|v\|² |
| `nullify (x : Nat) : Nat := if x >= 500 then x else 0` | 3 | hard-coded Δ (Grand_Unified) |

Remainder: 2 files define `R := x - N` (Core, Nullification_Complete_v4, EnergyFlow_v4); all others define `if … then 0 else x`. Extensionally equal on every carrier; `nsa_spectral_bridge_part2` calls it `reservoir`.

---

## 1. Catalogue of operations beyond the plain projector

Each entry: **definition** (quoted) · **theorems** with status and file · **relation to N and R** · (c) where the hackathon touched it.

### 1.1 Remainder R and conservation N + R = id

**(a)** `Nullification_Core.lean`:
```lean
theorem conservation (Δ : ℝ) (x : ℝ) : nullify Δ x + remainder Δ x = x := by simp only [remainder, add_sub_cancel]      -- proved (by definition of R)
theorem remainder_bounded (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : |remainder Δ x| < Δ ∨ remainder Δ x = 0                       -- proved
```
`Batch1_Classification_aristotle.lean` (ℕ, Aristotle-proved, 10/10): `conservation`, `R_zero`, `R_at_threshold : R Δ Δ = 0`, `remainder_when_nullified : classify Δ x = nullified → R Δ x = x`, `remainder_when_observable`, `remainder_bound`, plus exhaustiveness/uniqueness of the three classes.
`Batch2_Monotonicity_aristotle.lean`: `R_comp_N : R Δ (N Δ x) = 0`, `N_comp_R : N Δ (R Δ x) = 0` — **the two operators annihilate each other's output** (proved).
`output97_nsa_comparison-1.lean` (ℝ): `nullify_routes_intact (h : |x| ≥ Δ) : nullify Δ x = x`, `remainder_stores_intact (h : |x| < Δ) : remainder Δ x = x`, `nullify_kills_subthreshold`, `subthreshold_content_recoverable (h : IsReservoir Δ x) : nullify Δ x = 0 ∧ remainder Δ x = x`, `routing_functor_theorem` (the four-way split) — all proved.
`output89_nlos_projection_duality.lean`: `nlos_conservation`, `observable_no_remainder`, `hidden_content_is_remainder`, `remainder_in_evanescent` — proved.
List form (`Batch3_Distributivity_aristotle.lean`): `sumN Δ xs + sumR Δ xs = sumList xs` is proved only for `[]`, `[x]`, and `[3,12]` (`list_conservation_empty/_singleton/_example`); the general list statement `list_conservation` is **sorry** in `Nullification_Aristotle_Extension.lean` (never closed in the `_aristotle` copy either — that copy still has 26 sorries).
Energy-pool form (`Nullification_EnergyFlow.lean`): `energy_conservation : rawEnergy h = totalMass h + cancelledEnergy h` — **sorry** ("Provable by induction on list structure"); the v4 file replaces it by three numeric `example`s.

**Relation.** R is the unique companion making N + R = id; the corpus never defines R independently of N except as the `if` branch. "R does work" (OTOC map §2) is a prose claim; the only theorems about R are the ones above (bounded, stores intact, annihilated by N).

**(c)** inventory B1 (remainder proxy from two χ rungs, fails kill criterion), B2 (list conservation across a threshold ladder → Richardson in threshold, negative in emulator).

### 1.2 Idempotence, image, fixed points, composition

**(a)** `Nullification_Core.lean`: `idempotent (Δ : ℝ) (hΔ : 0 ≤ Δ) (x : ℝ) : nullify Δ (nullify Δ x) = nullify Δ x` — proved. (Every ℝ copy carries a hypothesis `0 ≤ Δ` or `0 < Δ`; it is superfluous — see §4.9.)
`Batch5_Image_aristotle.lean` (ℕ, Aristotle 10/10; one proof is `exact?`):
```lean
theorem in_image_N (Δ : Nat) (x : Nat) : (∃ y, N Δ y = x) ↔ (x = 0 ∨ x >= Δ)
theorem gap_not_in_image (Δ : Nat) (x : Nat) (h1 : 0 < x) (h2 : x < Δ) : ¬∃ y, N Δ y = x
theorem fixed_point_iff (Δ : Nat) (x : Nat) : N Δ x = x ↔ (x = 0 ∨ x >= Δ)
theorem N_triple (Δ : Nat) (x : Nat) : N Δ (N Δ (N Δ x)) = N Δ x
theorem N_projection (Δ : Nat) : ∀ x, N Δ (N Δ x) = N Δ x := by exact?
```
ℝ version: `nullify_fixed_iff (Δ : ℝ) (hΔ : Δ > 0) (x : ℝ) : nullify Δ x = x ↔ |x| ≥ Δ ∨ x = 0` (output97, proved via `grind`), `agreement_locus_subthreshold : {x | |x| < Δ ∧ nullify Δ x = x} = {0}` (proved).
Classification level (`Batch14_Information_Enforcement.lean`, proved): `reservoir_collapses_to_ground`, `observable_stays_observable`, `ground_stays_ground` — N maps [0.0e] → [0], [1] → [1], [0] → [0].
`Nullification_Robinson_Correspondence.lean` (Float, **no theorems**, `#eval` only) states the structural reading: N is a *retraction* onto im(N) = {0} ∪ {|x| ≥ Δ}, R a retraction onto {|x| < Δ}, and N is **not** a ring homomorphism (counterexamples 0.6+0.7 and 0.6×2.0). It explicitly retracts the earlier claim "N is isomorphic to st()".

**(c)** inventory C1: pauli-path draws with the same (threshold, max_paulis) are bit-identical (16/16) — idempotence on platform draws; A2: fixed point of the χ-ladder as class [1] (G3 q19 at −1.000, not calibratable).

### 1.3 Monotonicity — in x and in Δ

**(a)** `Batch2_Monotonicity_aristotle.lean` (ℕ, proved):
```lean
theorem N_monotone (Δ : Nat) (x y : Nat) (h : x ≤ y) : N Δ x ≤ N Δ y
theorem threshold_monotone (Δ₁ Δ₂ : Nat) (x : Nat) (h : Δ₁ ≤ Δ₂) : N Δ₂ x ≤ N Δ₁ x
theorem at_threshold (Δ : Nat) (hΔ : Δ > 0) : N Δ Δ = Δ
theorem just_below_threshold (Δ : Nat) (hΔ : Δ > 0) : N Δ (Δ - 1) = 0
```
Real version: `MdBatch4.lean` `theorem_125_accumulation_is_monotonic (Δ : Real) (x : Real → Real) (hx : Monotone x) (hΔ : 0 ≤ Δ) : Monotone (fun t => N Δ (x t))` — proved, but for the **one-sided** `N (Δ x : Real) := if x ≥ Δ then x else 0` of that file, not the Core `|x|` operator.
The AFM v7 paper (P2) says "N(Δ,·) is monotone above threshold".

**(b)** For the Core (two-sided) operator on ℝ: x-monotonicity **holds** (case check: if |x| < Δ ≤ |y| with x ≤ y then y ≥ Δ > 0 ≥ … ; all cases close), but **Δ-monotonicity as stated is false** for negative x: x = −1, Δ₁ = ½, Δ₂ = 2 gives N_{Δ₂}x = 0 ≰ −1 = N_{Δ₁}x. The correct real statement is `|nullify Δ₂ x| ≤ |nullify Δ₁ x|`. Nobody has written it. The OTOC map's "monotonicity" should be read as the ℕ/|·| version.

### 1.4 Dilation covariance ("only x/Δ matters")

**(a)** Stated in `explore/MNF_x_OTOC_map.md` §1 and used in the inventory (§H). **Not present anywhere in the Lean corpus as a statement about N.** Grep `dilat|homogen|scale_invar` over the 301 files hits exactly one declaration, `NullificationProofs.lean:180` `same_wall_scale_invariance` (also in the `__1_`/`__2_` copies): its hypotheses are three correlation records at QCD / black-hole / Hubble scale and its conclusion is `… → True`, proved by `intro _; trivial` — a True-stub about the reservoir's correlation with boundaries at different physical scales, saying nothing about N(cΔ, cx). The only other "scaling" theorems are Batch17's `holes_preserved_under_scaling`, about a record field, and `PreContinua` `refinement_preserves (h : Δ' ≤ Δ) (hx : x ≥ Δ) : x ≥ Δ'`.
Closest formal content: `output97` `reclassification_by_scale (h₁ : |x| ≥ Δ₁) (h₂ : |x| < Δ₂) : IsObservable Δ₁ x ∧ IsReservoir Δ₂ x ∧ nullify Δ₁ x = x ∧ remainder Δ₂ x = x` and `IsInShell Δ₁ Δ₂ x := |x| ≥ Δ₁ ∧ |x| < Δ₂` with `N_disagrees_across_scales` — the **shell structure**: the same x changes class as Δ moves. `Nullification_PreContinua_Fixed__1_.lean` defines `refineResolution pc := ⟨pc.resolution * 2, pc.threshold / 2⟩` (def-only) — a Δ-halving dynamics under which [0.0e] content becomes [1].

**(b)** Proposed, trivially provable from the definition: `nullify (c*Δ) (c*x) = c * nullify Δ x` and `classify (c*Δ) (c*x) = classify Δ x` for `c > 0` (fails for c < 0 unless |c| is used). Scale is the one parameter the framework has, and it is where injection/ejection can be *driven* without touching content (§3.2).

**(c)** inventory H: correlation scoring is scale-free, so global c·v post-processing is null; per-ID relative thresholds (relN) are the dilation-covariant classifier.

### 1.5 Spectral gap, gap emptiness, discreteness, master enforcement

**(a)** Core: `spectral_gap … : nullify Δ x = 0 ∨ |nullify Δ x| ≥ Δ`, `gap_empty … : ¬(0 < |nullify Δ x| ∧ |nullify Δ x| < Δ)` — proved.
`Batch14_Information_Enforcement.lean` / `Batch14_MasterEnforcement.lean` (ℕ; the second is the Aristotle copy, UTF-8 double-encoded on disk, §4.17):
```lean
def Unitary (Δ : ℕ) : Prop := ∀ x, N Δ x + R Δ x = x
def DiscreteTransitions (Δ : ℕ) : Prop := ∀ x, N Δ x = 0 ∨ N Δ x ≥ Δ
def SpectralGapProperty (S : Set ℕ) (Δ : ℕ) : Prop := ∀ x ∈ S, x = 0 ∨ x ≥ Δ
theorem master_enforcement (Δ : ℕ) (hΔ : Δ > 0) :
    (∀ x, N Δ x + R Δ x = x) ∧ (∀ x, N Δ (N Δ x) = N Δ x) ∧ (∀ x, N Δ x = 0 ∨ N Δ x ≥ Δ)   -- proved
theorem unitarity_and_discrete_implies_gap … : Unitary Δ ∧ DiscreteTransitions Δ → SpectralGapProperty {x | ∃ y, N Δ y = x} Δ   -- proved
theorem no_gap_violates_discrete …   -- proved
```
`pair1_master_enforcement_CONTENT.lean` is the AXLE-submitted pair (paper says AXLE id e0755420…; the STATEMENT side is `by sorry` by design). `HPContext.lean` re-proves it on ℝ as `master_enforcement_local (Δ : ℝ) : SpectralGapProperty (Set.range (N Δ)) Δ` (proved, and here no `Δ > 0` is needed).
Note the prose "Theorem 140: the gap is EQUIVALENT to conservation ∧ idempotence ∧ discreteness" — the theorem proves the conjunction, not an equivalence; and the "enforcement" theorem 138 has `Unitary` as an unused hypothesis (the gap follows from `DiscreteTransitions` alone, which is itself `nullification_discrete`, i.e. the definition). The framework-level content is: **the gap is the definition of N read on its range**; `HPContext.lean` is where the transfer to any other set is isolated as the open step: `structure HPContext (Δ : ℝ)` bundles `zetaShift`, `zeroSet`, `shiftedSpec` and the field `N_targets : Set.image zetaShift zeroSet ⊆ Set.range (N Δ)`; `hp_correspondence_transfers_gap (ctx : HPContext Δ) : SpectralGapProperty ctx.shiftedSpec Δ` is proved in three lines from `master_enforcement_local` and `ctx.N_targets`, and the file's own docstring says that supplying a `HPContext` "is the single Hilbert–Pólya identification step the paper explicitly does not prove".

### 1.6 Non-distributivity, pool accumulation, list sums, partition vs power

**(a)** Core (ℝ): `not_linear (hΔ : 0 < Δ) : ∃ x y, nullify Δ (x + y) ≠ nullify Δ x + nullify Δ y` (witness Δ/2 + Δ/2) and
`accumulation_crosses_threshold (hΔ : 0 < Δ) (n : ℕ) (hn : n ≥ 2) : ∃ x, |x| < Δ ∧ |n • x| ≥ Δ` (witness Δ/n) — proved.
`Batch3_Distributivity_aristotle.lean` (ℕ, 10/10): `distributive_when_both_survive (ha : a ≥ Δ) (hb : b ≥ Δ) : N Δ a + N Δ b = a + b`, `distributive_sum_survives`, `non_distributive_example : N 10 (6+6) ≠ N 10 6 + N 10 6`, `accumulation_possible : ∃ xs, (∀ x ∈ xs, classify 10 x = nullified) ∧ sumR 10 xs ≥ 10` (witness [3,3,3,3]), `five_threes_accumulate`; `sumR Δ xs := xs.foldl (fun acc x => acc + R Δ x) 0`.
`output97`: `N_not_additive`, `homomorphism_gap : st additive ∧ N not` (proved); `output88_cube_projection-1.lean` (ℝ): `pool_threshold_exists (hΔ : 0 < Δ) : ∃ a b c, classify Δ a = reservoir ∧ … ∧ classify Δ (compose3 a b c) = observable` (witness Δ/2 ×3) — proved; `output92`: `pool_sum`, `signed_pool_pos_crosses_threshold (ha : Δ/3 ≤ a) … : Δ ≤ pool_sum [a,b,c]`, `pool_pos_stays_positive`, `pools_have_opposite_signs` — proved (all `linarith`).
`Nullification_Geometry.lean`: vector non-distributivity `(4,3)+(5,5) → (9,8), 145 ≥ 100` is **`#eval` only**; the two theorems there are `componentwise_conservation` and `norm_conservation` (proved).
Partition vs power (`Batch12_PartitionPower_Aristotle_aristotle.lean`, 9/10 Aristotle-proved): `additive_accumulation_crosses_threshold` ([3,3,4] partition of 10, `sumR 10 = 10`), `additive_vs_multiplicative_dynamics` (`sumR 10 [3,3,3,3,3] ≥ 10 ∧ R 10 (3^1) = 3 ∧ R 10 (3^2) = 9 ∧ R 10 (3^3) = 0`), `spectral_gap_separates_dynamics`, `partition_count_avoids_powers`; **`messina_ono_concrete` was negated by Aristotle** (`sumList [4,3,…,3,1] = 42` is false: that list sums to 41) and left as `sorry`; `Theorem120_Fix.lean` restates it with [6,6,6,6,6,6,6] and still ends in `sorry`.
Half-threshold prevention (`output98_multizone_optimization-1.lean`, proved): `gradient_prevents_pool (ha_half : a < Δ/2) (hb_half : b < Δ/2) : a + b < Δ`, `half_threshold_prevents_all_pool_events`, `gradient_spike_causes_typeA_failure`.

**Relation.** This is the only place the framework is non-trivial: N is a retraction, not a homomorphism, and R's values sum. The physical word for "sum sub-threshold pieces, then apply N" is *pool accumulation*; in operator terms it is `N ∘ Σ ≠ Σ ∘ N`.

**(c)** This is the theorem that paid: inventory D1/D2 (v5 373 > v7 326; 9/9 pairs the compact expansion keeps the larger |v|); STATUS 08:10 ("fragmented ones shrink toward 0 or flip sign").

### 1.7 Pools, cycles, emission — the operational (def-only) dynamics

These are the only places where content is moved *into* or *out of* a reservoir as an operation (relevant to §3):

| file | definition (verbatim) | status |
|---|---|---|
| `Nullification_Phase3_Convergence__1_.lean` | `def cycleStep (Δ : Nat) (s : CycleState) (input : Nat) : CycleState := let total := s.remainder + input; let newObs := nullify Δ total; let newRem := remainder Δ total; ⟨s.observable + newObs, newRem⟩` and `runCycle Δ inputs := inputs.foldl (cycleStep Δ) ⟨0, 0⟩` | def-only, `#eval` |
| `Nullification_Phase2_Web.lean` | `def poolCrosses (Δ : Nat) (xs : List Nat) : Bool := sumRemainders Δ xs >= Δ` | def-only |
| `BlackHole_Singularity_Resolution.lean` | `def hawking_emission (reservoir_total : Nat) : Nat := N reservoir_total`; `def evaporation_step (reservoir : Nat) (chunk : Nat) : Nat × Nat := let emission := if chunk >= MASS_GAP then chunk else 0; let remaining := reservoir - chunk; (emission, remaining)` | `accumulation_crosses`, `singularity_resolution`, `information_preserved` proved by `native_decide` on literals; `evaporation_step` def-only |
| `Nullification_Complete_Zenodo.lean` | same `hawking_emission`; `accumulation_emits : hawking_emission (accumulate [1000,1000]) = 2000` | native_decide |
| `Complete_Nullification_Framework.lean` | `def evolve : UniverseState → UniverseState \| quantified => nullified \| nullified => quantified`; `theorem cycle_returns : ∀ s, evolve (evolve s) = s`; `toUniverseState reservoir = nullified` | proved (2-element enum) |
| `Ramanujan_Temporal_MassGap__1_.lean` | `next_state : quantified ↦ infinitesimal ↦ undefined ↦ quantified` ("[1] → [0.0e] → [0] → [1]"); `three_cycle_returns`; `transition_energy infinitesimal quantified = MASS_GAP`, `transition_energy quantified infinitesimal = 0  -- [1] → [0.0e] releases` | proved (enum); 1 sorry elsewhere (Nat division) |
| `Nullification_EnergyFlow.lean` | `inductive SelectionRule \| conserved \| cancelled \| gauge \| accumulated`; `def poolClass (Δ : ℕ) (p : EnergyPool) : EnergyClass := if ¬(poolContributes p) then zero else classify Δ p.energy` | 3 sorry (conservation over the list, case analysis, `energy_flow_principle`) |

`cycleStep` is, formally, **inject-then-nullify**: the input is added to the stored remainder, N takes what crosses, R keeps the rest. It is the only object in the corpus that is a reservoir *with state*. It has no theorem.

### 1.8 Degenerate zeros — types A, B, C and the "unified" form

**(a)** `Batch4_2_DegenerateZeroMechanisms-1.lean` (ℕ/ℤ):
```lean
def IsDegenerateZero_TypeA (Δ : ℕ) (x y : ℕ) : Prop := N Δ x = 0 ∧ N Δ y = 0 ∧ N Δ (x + y) ≠ 0
def IsDegenerateZero_TypeB (Δ : ℤ) (x y : ℤ) : Prop := |x| ≥ Δ ∧ |y| ≥ Δ ∧ x + y = 0 ∧ x ≠ 0
def IsDegenerateZero_Unified (probe_zero : Prop) (content_nonzero : Prop) : Prop := probe_zero ∧ content_nonzero
theorem typeA_is_nondistributive (h : IsDegenerateZero_TypeA Δ x y) : N Δ x + N Δ y ≠ N Δ (x + y)   -- proved
theorem typeB_zero_is_equatorial : signed_classify_int 1 (charge_xi_minus + charge_xi_c_plus) = ground ∧ … observable ∧ … observable   -- decide
```
Its headline instance `xi_typeA_degenerate : IsDegenerateZero_TypeA Λ_QCD m_strange m_strange` is **false** (96 + 96 = 192 < 246), as `Batch4_3_TriangleDegenerateZero.lean` records; Batch4_3 therefore redefines
```lean
def IsDegenerateZero_TypeA (Δ : ℕ) (x y z : ℕ) : Prop := N Δ x = 0 ∧ N Δ y = 0 ∧ N Δ z ≠ 0 ∧ z > x + y
def IsDegenerateZero_TypeC (Δ : ℕ) (x y w z : ℕ) : Prop := N Δ x = 0 ∧ N Δ y = 0 ∧ N Δ w = 0 ∧ N Δ z ≠ 0 ∧ z > x + y + w
theorem cascade_amplification_condition … : IsDegenerateZero_TypeA Δ x y z := ⟨hx, hy, hz, hbind⟩   -- proved (it is the constructor)
theorem binding_energy_positive (h : IsDegenerateZero_TypeA Δ x y z) : z - (x + y) > 0   -- proved
```
with the combined state z an **independent parameter** ("you cannot compute z from x and y alone"). So the corrected Type A is no longer a statement about N at all — any z ≥ Δ with z > x + y satisfies it. The *mechanism* (sum crosses) is Batch3's; the *corrected definition* is a record of four facts.
Type B needs the signed classes (§1.9): two observables of opposite sign summing to 0 — "zero in one probe dimension, nonzero content in another". Batch4_1's `xi_minus_neg_reservoir`/`xi_c_plus_pos_reservoir` (charges ±1 at `charge_threshold = 1` claimed to be reservoir) are **false as written** (|±1| ≥ 1 ⇒ observable); Batch4_2's own in-file §5 documents Aristotle finding this and reinterprets it as Type B. `Batch4_1` also contains `axiom ibm_mass_gap_positive : (192 : ℝ)/100 > 0` — an arithmetic triviality declared as an axiom "proved experimentally".

**Relation.** Type A = non-distributivity with the sum hidden; Type B = cancellation inside the [1] class (nothing to do with N's threshold — `x + y = 0` is additive cancellation); Type C = Type A with three parts. The word "degenerate" is used for both (A) a reservoir that *looks* empty to N and (B) a pool that *is* zero by cancellation — these are different objects and should be kept apart when reading the OTOC data.

**(c)** inventory A3 (an exact-0 PP draw is [0.0e]/missing, not [0]: +0.013 r² on S3), E3 (Type-B "equatorial" reading killed: z ≈ 0 with large |r| carries no z sign on S3), and the G4 sign-consistency gate (STATUS 08:09: 3 IDs with draws of both signs set to 0 → 48 → 118) — which is Type B used as a *filter*, not Type A.

### 1.9 Signed nullification ±0.0e and signed multiplicity

**(a)** `output56_signed_nullification.lean` (ℤ and ℝ, Mathlib; 35 theorems, 0 sorry):
```lean
inductive SignedNullClass | ground | pos_reservoir | neg_reservoir | observable
def N_int (Δ : ℤ) (x : ℤ) : ℤ := if |x| ≥ Δ then x else 0
def R_int (Δ : ℤ) (x : ℤ) : ℤ := if |x| ≥ Δ then 0 else x
def signed_classify_int (Δ : ℤ) (x : ℤ) : SignedNullClass :=
  if x = 0 then ground else if |x| ≥ Δ then observable else if x > 0 then pos_reservoir else neg_reservoir
def forget_sign : SignedNullClass → NullClass   -- pos/neg_reservoir ↦ reservoir
```
Proved: `signed_conservation`, `signed_idempotent (hΔ : 0 ≤ Δ)`, `signed_mass_gap`, `reservoir_sign_pos/neg : R_int Δ x > 0 ↔ (x > 0 ∧ |x| < Δ)`, `forget_sign_surjective`, `signed_refines_unsigned`, `pos_reservoir_empty_int`/`neg_reservoir_empty_int`/`signed_binary_at_one_int` (on ℤ at Δ = 1 both reservoirs are empty — discreteness), `pos_reservoir_nonempty_real`/`neg_…` (¼ and −¼ at Δ = ½), `signed_strictly_finer`.
Composition (Part 7–8): `SignedTriple` with `pos_count`/`neg_count`, `is_coherent := pos_count = 0 ∨ neg_count = 0`, `is_degenerate := pos_count > 0 ∧ neg_count > 0`, `coherent_iff_not_degenerate` (proved), `compose_real a b c := a + b + c`, `coherent_pos_sum_pos`, `mixed_can_cancel (hε : ε > 0) : compose_real ε ε (-2*ε) = 0`, `coherent_pos_no_cancel`, `pos_pool_crosses_threshold` (three positive sub-threshold values whose sum ≥ Δ are all `pos_reservoir` and the sum is `observable`) — proved.
Spectral: `signed_gap_forces_ground (h_gap : SpectralGapProperty ShiftedZeroSpectrum (1/2)) (ρ) (hρ) : signed_classify_zero ρ hρ = ground` — proved (uses only the strip bound).
`output57_signed_multiplicity.lean` (19 theorems, 0 sorry): multiplicity deviation `mult_deviation_int ρ := (zeta_order ρ : ℤ) - 1` is one-sided; `one_sided_sum_zero_iff (ha : 0 ≤ a) … : a + b + c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0` — "no false ground on a one-sided spectrum" (proved, omega); `two_sided_false_ground_exists : ∃ a b c : ℤ, a + b + c = 0 ∧ a > 0 ∧ c < 0`; `mult_binary_classification`, `signed_multiplicity_resolution` (under four named hypotheses incl. `SpeiserStrengthened`). `output71_signed_resolution.lean` merges 56+57 (`zeta_order_ge_one` proved there).
`output92_signed_depth_multiplexing.lean` (41 theorems; the one `sorry` match is prose): signed pools stay sign-separated.

**Relation.** The sign refinement is where the corpus goes beyond a projector: N is sign-preserving on [1] (`preserves_sign`), R is sign-preserving on [0.0e] (`reservoir_sign_pos/neg`), and the coherent/degenerate dichotomy is a property of *sums of R-values*, i.e. of the pool, not of N.

**(c)** inventory E1 (coherent-sign triple across χ rungs: killed on MPS), E2 (same across PP draws: killed a priori — by D2 the odd-sign draw is the fragmented one); STATUS G4_v7 (sign gate +70) and G4_v9 (sign-only lost: magnitudes carry information).

### 1.10 Probes: NorthProbe / SouthProbe, Dev / ConjDev, Δ/2

**(a)** Origin, `output86_pole_probe-1.lean` (RH setting, Mathlib; 19 theorems, 1 real `sorry` + 1 `axiom`):
```lean
noncomputable def NorthProbe (ρ : ℂ) : ℝ := ρ.re - 1/2
noncomputable def SouthProbe (ρ : ℂ) : ℝ := -(ρ.re - 1/2)
theorem probe_balance_always (ρ : ℂ) : NorthProbe ρ + SouthProbe ρ = 0          -- proved (definitional)
theorem north_probe_zero_iff (ρ : ℂ) : NorthProbe ρ = 0 ↔ ρ.re = 1/2              -- proved
noncomputable def signed_position (Δ : ℝ) (ρ : ℂ) : SignedNullClass := … NorthProbe ρ …
axiom func_eq_deriv : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → deriv riemannZeta (FuncEqPartner ρ) = 0 ↔ deriv riemannZeta ρ = 0
theorem rh_and_speiser_implies_simple … := by … sorry -- [Levinson-Montgomery 1974: to be filled by Aristotle]
```
(The header says "Zero sorry. Zero exact?. Zero admit." — it has one of each of the first two kinds: the sorry at line 449 and `pole_probe_capstone` depends on it.)
Paper names, `LevelingTheorem_PaperFacing.lean` / `pair2_leveling_*`: `def Dev (ρ : ℂ) : ℝ := ρ.re - 1/2`, `def ConjDev (ρ : ℂ) : ℝ := -(ρ.re - 1/2)`, `dev_plus_conjdev_zero`, `conjdev_eq_neg_dev`, `dev_func_eq_partner : Dev (1 - ρ) = -(Dev ρ)` — proved.
Threshold form, `MNFmeetsDavisSet3_2.lean`, `MNFmeetsDavisSet4.lean`, `wormhole_3_bypass_v2-1.lean`, `wormhole_4_ejection_thorne-1.lean`, `mnf_wormhole_nsa_merged.lean`:
```lean
noncomputable def NorthProbe (Δ : ℝ) (x : ℝ) : ℝ := x - Δ / 2
noncomputable def SouthProbe (Δ : ℝ) (x : ℝ) : ℝ := -(x - Δ / 2)
def PositiveReservoir (Δ : ℝ) (hΔ : Δ > 0) (x : ℝ) : Prop := x > 0 ∧ x < Δ
theorem probe_balance (Δ : ℝ) (x : ℝ) : NorthProbe Δ x + SouthProbe Δ x = 0                 -- proved
theorem north_probe_zero_iff (Δ : ℝ) (x : ℝ) : NorthProbe Δ x = 0 ↔ x = Δ / 2                 -- proved
theorem probe_balance_encodes_conservation (Δ x : ℝ) : NorthProbe Δ x + SouthProbe Δ x = 0 ↔ nullify Δ x + remainder Δ x = x   -- proved: both sides are always true
theorem wormhole_leveling_north (h : PositiveReservoir Δ hΔ x) : |NorthProbe Δ x| < Δ / 2       -- proved
theorem bounded_probes_imply_bypass (h_north : |NorthProbe Δ x| < Δ/2) (h_nonzero : x ≠ 0) : ¬ IsObservable Δ x   -- Set3_2: ends in `exact?` (Aristotle stalled); Set4: re-proved as `_fixed` with the extra hypothesis `x > 0`
```
DMD variant (`output87_dmd_projection-1.lean`): `NorthProbe_dmd (cfg) (Δ)`, `NorthProbe_single (Δ) (x_tilt)` — the same `x − Δ/2` on mirror tilt.

**Relation to N/R.** A probe is an affine recentring `x ↦ x − Δ/2`; its only link to N is `probe_balance_encodes_conservation`, an `↔` between two unconditionally true statements. The "balance condition" is `a + (−a) = 0`. The probes carry **no threshold information by themselves**; what they add is a *signed* reading of distance from the midpoint of the band (0, Δ).

**Δ/2 vs Δ, and the scale mismatch.** In the RH setting the band is the strip (0, 1), midpoint ½, and the gap threshold is **also** ½: `SpectralGapProperty S (1/2)` says |Dev| = 0 or ≥ ½ while the strip gives |Dev| < ½ — a genuine squeeze to Dev = 0 (`leveling_theorem`). In the wormhole transcription the band is (0, Δ) with midpoint Δ/2, but the gap threshold is left at **Δ**, so the analogous squeeze would need a gap at Δ/2 on the *probe* value, which no wormhole file assumes or proves. Consequently `wormhole_leveling_north` only proves **boundedness** `|probe| < Δ/2` (a restatement of 0 < x < Δ), not leveling to a point. The name "leveling theorem" in the wormhole files does not denote the same kind of result as in output86 (§4.5).

### 1.11 Leveling theorem, tau-half, Bridge78 generalisation

**(a)** `output86`: `leveling_theorem (h_gap : SpectralGapProperty ShiftedZeroSpectrum (1/2)) (ρ) (hρ) : NorthProbe ρ = 0`; `poles_agree_implies_on_line`; `spectral_gap_implies_rh` — proved. `pair2_leveling_CONTENT.lean` / `LevelingTheorem_PaperFacing.lean`: `leveling_theorem … : Dev ρ = 0`, `leveling_implies_re_half`, `spectral_gap_implies_rh : … → RiemannHypothesis` — proved (PaperFacing imports `lean_files.LevelingTheorem`, which is not in the folder, §4.8). AXLE id 376a6860… per the paper.
`tau_half_real (S : Set ℝ) (h_bound : ∀ x ∈ S, |x| < 1/2) (h_gap : SpectralGapProperty S (1/2)) : S ⊆ {0}` — proved in `full_cascade_loop_breaker`, `pair3`, `output72`, `GUE_Comprehensive`, `EmpiricalBridge` …; `tau_half_nat` likewise. **Despite the name, `tau_half` has nothing to do with τ/2 = π**; it is the squeeze lemma at threshold ½ (§4.6).
`MNF_Bridge78.lean` (namespace `MNF.Bridge78`, imports only `Mathlib.NumberTheory.LSeries.RiemannZeta`, `#print axioms` block at the end, 0 sorry): `tau_threshold (h_bound : ∀ x ∈ S, |x| ≤ c) (hcΔ : c < Δ) (h_gap : SpectralGapProperty S Δ) : S ⊆ {0}` (general threshold), `on_line_of_gap`, `gap_of_on_line` (converse), `riemannHypothesis_iff_gap (h78 : ZeroFreeRightOf (7/8)) (hΔ : 3/8 < Δ) : RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ`, and three kernel-checked no-go countermodels (`analytic_no_go`, `structural_inputs_insufficient`, `euler_type_no_go`). This file is the most carefully registered in the corpus ([WRAPPER]/[TRIPWIRE], hypothesis `ZeroFreeRightOf (7/8)` never discharged).

**Relation.** The leveling theorem is **N-free**: it is `tau_half_real` applied to the shifted zero set. N enters only by name (`SpectralGapProperty` is the gap on im N transferred by hypothesis). The paper (AFM v7 §8.1) says exactly this: the gap "should not be interpreted as strictly weaker than RH … the two are equivalent by the bounded strip".

### 1.12 EJECTION — every definition and theorem

Three unrelated formalisations share the word.

**(i) Toroid ejection point = π** (`Batch17_ToroidNullification.lean` §6; Aristotle copy `batch17.lean`):
```lean
def EjectionPoint : ℝ := Real.pi
def ThreeStateConvergence : Prop := ∃ (zero_state res_state obs_val : ℝ),
    zero_state = 0 ∧ 0 < res_state ∧ res_state < EjectionPoint ∧ obs_val = EjectionPoint ∧ zero_state + res_state < obs_val
theorem three_state_convergence_exists : ThreeStateConvergence                    -- proved (witness 0, 1, π)
theorem zero_ejects_only_at_ejection_point : ∀ θ : ℝ, θ = EjectionPoint → ∃ convergence : ThreeStateConvergence, True   -- proved; conclusion is vacuous
theorem tau_half_is_pi : (2 * Real.pi) / 2 = Real.pi                                -- proved (ring)
theorem cascade_ejects_at_pi : ∀ n : ℕ, RamanujanPartialSum n < 1 / Real.pi ∧ (1 / Real.pi) > 0   -- first conjunct sorry
theorem ramanujan_cascade_converges_to_pi : Tendsto RamanujanPartialSum atTop (nhds (1 / Real.pi))   -- sorry (Aristotle: omitted)
theorem ramanujan_partial_sums_monotone (n : ℕ) : RamanujanPartialSum n < RamanujanPartialSum (n + 1)   -- proved
```
Content: an angle π on a torus, a positive real below π, and an unproved series identity. No operator moves anything.

**(ii) Tau geometry of the probes** (`wormhole_3_bypass_v2-1.lean` §3; `MNFmeetsDavisSet3_2.lean`): `tau := 2π`, `tau_north := tau/4`, `tau_south := 3*tau/4`, `tau_eject := tau/2`; `tau_eject_eq_pi`, `probes_straddle_ejection : tau_eject - tau_north = π/2 ∧ tau_south - tau_eject = π/2`, `probe_separation : tau_south - tau_north = π` — all proved by `ring`. These are arithmetic facts about the constants 2π/4, 2π/2, 3·2π/4; nothing connects `tau_eject` to `NorthProbe Δ x` or to Δ.

**(iii) Threshold ejection = reaching x = Δ** (`wormhole_4_ejection_thorne-1.lean`; Aristotle copy `MNFmeetsDavisSet4.lean`; merged file):
```lean
def IsEjectionThreshold (Δ : ℝ) (x : ℝ) : Prop := x = Δ
theorem ejection_probe_reading (Δ : ℝ) : NorthProbe Δ Δ = Δ / 2                         -- proved
theorem ejection_state_is_observable (Δ : ℝ) (hΔ : Δ > 0) : IsObservable Δ Δ              -- proved
theorem below_ejection_is_reservoir (h : PositiveReservoir Δ hΔ x) : ¬ IsObservable Δ x ∧ |NorthProbe Δ x| < Δ / 2   -- proved
theorem ejection_is_sharp_transition (h : PositiveReservoir Δ hΔ x) : NorthProbe Δ x < NorthProbe Δ Δ   -- proved; unfolds to x < Δ = h.2
theorem transit_conservation (Δ : ℝ) (x : ℝ) : nullify Δ x + remainder Δ x = x := nullify_conservation Δ x
def GeodesicFollowsGeometry : Prop := True                                               -- True-stub
def MNFTargetingLaw (Δ_x Δ_y Δ_z : ℝ) : Prop := ∃ vx vy vz, nullify Δ_x vx = 0 ∧ vx ≠ 0 ∧ …   -- "three reservoir values exist"
theorem mnf_targeting_law_satisfiable … : MNFTargetingLaw Δ_x Δ_y Δ_z   -- proved (witness Δ/2; Aristotle's proof ends in `skip` after a `use` chain)
theorem master_ejection_theorem (h : PositiveReservoir Δ hΔ x) : ¬ IsObservable Δ x ∧ |NorthProbe Δ x| < Δ/2 ∧ IsObservable Δ Δ ∧ NorthProbe Δ Δ = Δ/2 ∧ NorthProbe Δ x < NorthProbe Δ Δ ∧ (∀ v, nullify Δ v + remainder Δ v = v) ∧ MNFTargetingLaw Δ Δ Δ   -- proved (conjunction of the above)
```
`IsEjectionThreshold` is defined and never used in any theorem. `MNFmeetsDavisSet4` re-states the same theorems with `_fixed`/`_final` suffixes (Aristotle: "to resolve ATP state conflicts"); `gr_and_mnf_are_complementary` there ends in `exact?`.
Cascade vocabulary (`Batch17` §7, proved): `IsConfinedCascade (Δ) (seq : ℕ → ℕ) := ∀ n, N Δ (seq n) = 0`, `IsCriticalCascade := IsConfinedCascade ∧ Tendsto (seq) atTop (nhds Δ)`, `confined_cascade_no_blowup : IsConfinedCascade Δ seq → ∀ n, seq n < Δ`, `critical_cascade_remains_confined := h.1`. A *critical* cascade approaches Δ from below and never ejects — ejection is excluded by definition.

**What "ejection" is, formally.** (a) A **predicate on the boundary point** x = Δ of the positive reservoir band, with the facts that Δ itself is [1] (because the definition uses ≥) and that NorthProbe reads Δ/2 there. It is **not an operator**, has **no dynamics** (no x(t), no rate), and **no energy accounting** (`transit_conservation` is the unconditional identity). The toroid version is an angle. The two are linked only by the comment "τ/2 = π (Batch17 toroid ejection)".
(b) The only *operations* in the corpus that realise ejection are: the sum-then-N of §1.6 (pool crosses), `cycleStep` (§1.7; `newObs := nullify Δ total`), `hawking_emission := N total`, and `evaporation_step` (the one place the reservoir is *decremented*). Ejection = `N` applied to a pool that has grown past Δ. There is no theorem that an ejected value is removed from the pool except by the explicit `reservoir - chunk` in `evaporation_step` (def-only).
(c) Data: STATUS 08:10 — G4's sub-resolution values are the band just below the platform's floor; the "regime indicator is whether the platform's values sit above its truncation floor". No ejection event is observable in a single draw; what the data shows is the *class* of each ID at the platform's Δ.

### 1.13 Cascades: TCO₃ collapse, loop breaker

**(a)** `Batch13_TCO3_Collapse.lean` (original, ℕ, 8 sorry) and `Batch13.lean` (Aristotle, 0 sorry):
```lean
structure BracketLayer where coherence : Nat; branches : List Nat   -- [ ]
structure AngleLayer   where accumulated : Nat; threshold : Nat       -- ⟨ ⟩
structure BraceLayer   where outcome : Option Nat                     -- { }
theorem collapse_condition (accumulated threshold : Nat) (h : accumulated ≠ 0) : accumulated >= threshold ↔ N threshold accumulated = accumulated   -- proved WITH h; NEGATED without it (witness 0,1)
theorem post_collapse_is_observable (Δ) (accumulated) (h_crossed : accumulated >= Δ) (h_nonzero : accumulated ≠ 0) : classify Δ accumulated = observable   -- proved with h_nonzero; NEGATED without (Δ = 0)
theorem unique_collapse_point (Δ) (h_Δ_pos : Δ > 0) (D : Nat → Nat) (h_start : D 0 = 0) (h_mono : ∀ t, D t <= D (t + 1)) (h_crosses : ∃ T, D T >= Δ) : ∃! τ, D τ >= Δ ∧ ∀ t < τ, D t < Δ   -- proved (Nat.find)
theorem collapse_irreversible … (h_crossed : accumulated_t >= Δ) (h_mono : accumulated_t <= accumulated_t') : accumulated_t' >= Δ   -- proved (le_trans)
theorem born_rule_weights (w1 w2) … : w1 <= total ∧ w2 <= total ∧ w1 + w2 = total   -- proved; no Born rule content
theorem tco3_master …   -- proved
```
The three `structure`s are defined and never used by any theorem. `unique_collapse_point` is the one genuine theorem: a monotone ℕ-sequence that crosses Δ has a unique first crossing time. `tco3_collapse_master_phone(_v2).lean` carry 2 sorry each.
`full_cascade_loop_breaker.lean`: `level1_spectral_gap_implies_rh` depends on `singleton_implies_rh`, which has a `sorry -- [SORRY-BOUNDARY]` in the `Re(ρ) ≤ 0` branch; `rh_implies_density_control := ⟨sorry, sorry, sorry⟩` (its `ZeroDensityControl` is a structure of three bare `Prop` fields — any three propositions, e.g. `True`, would satisfy it); `density_control_implies_simple` sorry; `simplicity_implies_rh_reverse` sorry; `effective_gap_18 : effective_gap_at 18 = 1/2` (6√2/(4√18)) proved. So `full_cascade` has **four open holes on the path and one on the side**, not "two sorry markers" as its header says. `aristotle_stress_test_synthesis.lean` re-declares `conservation`, `idempotent`, `spectral_gap_batch`, `master_enforcement`, `N_is_filtration`, `N_is_not_quotient` as **axioms** (lines 124–133) to assemble a synthesis — proved theorems demoted to axioms.

### 1.14 Master / information enforcement

**(a)** `Batch14_Information_Enforcement.lean` defines
```lean
def hasInformation (x : ℕ) : Prop := x > 0
def PreservesInformation (f : ℕ → ℕ) : Prop := ∀ x, hasInformation x → hasInformation (f x)
def LosesInformation (f : ℕ → ℕ) : Prop := ∃ x, hasInformation x ∧ f x = 0
```
and then **never uses them**. Under these definitions `LosesInformation (N Δ)` is *true* for every Δ > 1 (x = 1) and `PreservesInformation (N Δ)` is false — the opposite of the file's prose ("information preserved … the reservoir class is unstable"). `no_gap_means_information_loss : ∀ Δ > 0, ∀ x, (0 < N Δ x ∧ N Δ x < Δ) → False` is proved and is `gap_empty` renamed. `EntropyClass` + `classifyEntropy` is `NullClass` + `classify` renamed; `threshold_asymmetry : 2 = 2 * 1 := rfl`.

### 1.15 Toroid, topological protection

**(a)** `Batch17_ToroidNullification.lean` / `batch17.lean` / `Batch17_1_TopologicalCorrection.lean`:
```lean
structure ToroidConfig where hole_count : ℕ; body_count : ℕ; surface_class : NullClass; dimension : ℕ
def HasTopologicalProtection (c : ToroidConfig) : Prop := c.hole_count ≥ 1
def IsSimplyConnectedConfig (c : ToroidConfig) : Prop := c.hole_count = 0
def ToroidScale (base : ToroidConfig) (target_dim : ℕ) : ToroidConfig := { hole_count := base.hole_count, body_count := base.body_count * target_dim, … }
def MinimalToroid : ToroidConfig := { hole_count := 1, body_count := 7, surface_class := observable, dimension := 2 }
theorem holes_preserved_under_scaling … : (ToroidScale c n).hole_count = c.hole_count   -- proved (simp)
theorem hole_count_is_topological_invariant … : ∀ c' : ToroidConfig, c'.dimension = c.dimension → c'.hole_count ≥ 1   -- sorry; Aristotle: FALSE as stated; Batch17_1 replaces it
theorem body_cannot_reach_hole_continuously : ∀ Δ > 0, ∀ x, N Δ x = 0 ∧ x > 0 → classify Δ x = reservoir   -- proved
```
`body_cannot_reach_hole_continuously` is the only theorem in the file that mentions N; it says a nonzero sub-threshold value is class [0.0e]. "Topological protection" is `hole_count ≥ 1` on a record; `π₁ = ℤ × ℤ` appears only in comments. `wormhole_3`: `IsTopologicallyProtected (w : ℤ) := w ≠ 0`, `torus_has_nontrivial_winding : ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ m ≠ n` (witness 1, 2), `topological_protection_requires_no_energy (h) : IsTopologicallyProtected w := h`.

### 1.16 Wormhole: three-axis separation, throat, c⁴/G bypass

**(a)** `wormhole_1_three_axis.lean` (Aristotle copy `MNFmeetsDavisSet1.lean`): `InSpectralGap Δ hΔ x := x ≠ 0 ∧ |x| < Δ`, `IsObservable Δ x := |x| ≥ Δ`, `spectral_incompatibility : InSpectralGap Δ hΔ x → ¬ IsObservable Δ x` (proved: |x| < Δ and |x| ≥ Δ contradict), `nullified_stays_nullified`, `three_axis_spectral_separation`, `master_three_axis_theorem` — proved.
`wormhole_2_intersection.lean` (`Set2`): `IsThroatPoint Δ_x Δ_y Δ_z vx vy vz := nullify Δ_x vx = 0 ∧ vx ≠ 0 ∧ …` (three independent reservoir values), `IsHolePoint := vx = 0 ∧ vy = 0 ∧ vz = 0`, `throat_points_exist` (witness ±Δ/2), `throat_surrounds_hole`, `throat_is_stable` (idempotence ×3), `throat_stability_radius` (|v| < Δ ⇒ reservoir), `hole_is_unfillable : nullify Δ 0 = 0`, `hole_has_no_remainder : remainder Δ 0 = 0` — proved. "Three axes" = three scalars with three thresholds; no vector space, no intersection beyond conjunction.
`wormhole_3_bypass.lean` (v1): `spacetime_stiffness := (3e8)^4 / (6.674e-11)`, `OvercomesBarrier energy := energy ≥ spacetime_stiffness`, `c4_over_G_bypass : IsReservoir Δ hΔ x → ¬ IsObservable Δ x`, `master_bypass_theorem` — proved; **`prior_proposals_hit_barrier (hobs : IsObservable spacetime_stiffness energy) : OvercomesBarrier energy := hobs`** is false for negative energy (|e| ≥ s does not give e ≥ s); the term `hobs` does not type-check; Aristotle's `Set3_1` adds `he : energy ≥ 0`. v1 as on disk would not compile. v2 adds the probes (§1.10).
The "bypass" is `spectral_incompatibility` with Δ := c⁴/G: a reservoir value is not observable *at that threshold*. It is the definition of the classes.

### 1.17 NLoS projection duality (output89): N and R as complementary subspaces

**(a)** `output89_nlos_projection_duality.lean` (41 theorems, 0 sorry):
```lean
class NLoSContext (V W) [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] where
  H : V →ₗ[ℝ] W;  H_inv : W →ₗ[ℝ] V
  reconstruction : ∀ v : V, H_inv (H v) = v
  projection_works : ∀ w : W, H (H_inv w) = w
theorem nlos_duality … (ψ_desired : W) : ∃! φ : V, ctx.H φ = ψ_desired ∧ φ = ctx.H_inv ψ_desired   -- proved
theorem conservation_is_invertibility … [ctx : NLoSContext V V] (v : V) : ctx.H (ctx.H_inv v) = v := ctx.projection_works v   -- proved: it IS the class field
def N_nlos (Δ x : ℝ) : ℝ := if |x| ≥ Δ then x else 0 ;  def R_nlos …
def EvanescentSpace (Δ : ℝ) : Set ℝ := {x | x ≠ 0 ∧ |x| < Δ} ;  def PropagatingSpace (Δ : ℝ) : Set ℝ := {x | |x| ≥ Δ}
theorem evanescent_propagating_disjoint (Δ : ℝ) : EvanescentSpace Δ ∩ PropagatingSpace Δ = ∅   -- proved
theorem hadamard_orthogonal_inline (n : ℕ) : (hadamardMatrix n) * (hadamardMatrix n).transpose = (2^n : ℤ) • 1   -- long proof present; not verifiable here
theorem hadamard_is_pool_accumulation (n : ℕ) (hn : 0 < n) : (∑ _i : Fin (2^n), (1 : ℤ)) = (2^n : ℤ)   -- proved; it is Σ 1 = 2^n
structure NLoSDualityCorrespondence where conservation_is_invertibility : True; reservoir_is_evanescent : True; spectral_gap_is_cutoff : True; pool_is_hadamard_norm : True; reconstruction_is_projection : True   -- True-stub
```
**Relation.** The class assumes a two-sided inverse, so H is a linear isomorphism and the "duality" is `H ∘ H⁻¹ = id`. The N/R pair appears only as the scalar `N_nlos/R_nlos` with their own conservation; **no theorem connects H to N_nlos**. "Conservation is invertibility" is a field name. The one real structural statement — evanescent = R-range minus {0}, propagating = N-range minus {0}, disjoint and covering — is `spectral_trichotomy` again. The Hadamard "pool accumulation" is the normalisation 2ⁿ; the "evanescent/propagating" reading is the only place in the corpus where [0.0e]/[1] are called *complementary subspaces* — and on ℝ they are complementary *sets*, not subspaces (neither is closed under addition: that is non-distributivity).

### 1.18 NSA correspondence: routing vs forgetting, shells

**(a)** `batch11_nsa_equivalence_aristotle.lean`: `def standard_part (x threshold : Nat) : Nat := if x >= threshold then x else 0` and `nsa_standard_part_correspondence : ∀ x, nullify MASS_GAP x = standard_part x MASS_GAP := by intro x; rfl` — "N ≡ st()" is **true by definition** (st is defined as N). `Nullification_Robinson_Correspondence.lean` (Float, def-only) retracts the isomorphism claim and gives the corrected one: "N is the finite-threshold analog of st(), … a non-linear threshold retraction that permits pool accumulation". `output97`: `st_model (x : ℝ) : ℝ := x` (identity), `st_is_additive`, `st_has_no_remainder_channel`, `st_vs_N_agreement_locus`, `master_NSA_comparison` — proved; `nsa_spectral_bridge_part2.lean`: `axiom st_is_RingFlux_on_finite`; `RingFlux_vs_SphereFlux.lean`: ring flux (additive, st) vs sphere flux (threshold, N) — `ring_flux_homomorphism` proves commutativity of `+`.
The AFM v7 appendix A is the authoritative prose: "N is a routing operation … [content] remains accessible and recoverable via R".

### 1.19 Geometry: componentwise vs norm nullification; Bloch; sphere

**(a)** `Nullification_Geometry.lean` (ℕ, no Mathlib): `nullifyComponentwise Δ v := ⟨nullify Δ v.x, nullify Δ v.y⟩`, `nullifyNorm Δsq v := if v.normSq >= Δsq then v else Vec2.zero`, `classifyNorm`, `Vec3` analogues; theorems `componentwise_conservation` and `norm_conservation` (proved); the difference (v = (6,8): componentwise → (0,0), norm → kept) is `#eval` only.
`Nullification_Bloch.lean`: `BlochVec` scaled by 100, `purityThresholdSq := 10000`, `classifyBloch`, `nullifyBloch Δsq r := if r.normSq >= Δsq then r else ⟨0,0,0⟩`, `classifyNull`; Bell/GHZ/W records; **zero theorems** (`#eval` and `#check "string"` only). The map's "Bloch length is the convergence meter" has no Lean counterpart.
`Batch15_ThreeDSphere-1.lean` (24 theorems, 0 effective sorry): `sphereClassify Δ x` = `classify` with names center/surface/exterior; three "axes" `Axis1_ReDeviation s := s.re - 1/2`, `Axis2_ImSpacing ρ₁ ρ₂ := |ρ₁.im - ρ₂.im|`, `Axis3_MultiplicityDev order := order - 1`; `PassesSphere s order spacing := Axis1 s = 0 ∧ spacing > 0 ∧ Axis3 order = 0`; `master_sphere_theorem : PassesSphere s order spacing ↔ (s.re = 1/2 ∧ spacing > 0 ∧ (order = 1 ∨ order = 0))` — proved. The "sphere" is a conjunction of three unrelated predicates.
`Batch16_ZeroZeroE_Field-1.lean`: `ConfinementGeometry` records (string/triangle/disk/sphere/trapezoid/heptagon), `TransitionRule g Δ` (existence of sub-threshold components and a super-threshold z), `zero_zero_e_shell_definition : N Δ x = 0 ∧ x > 0 ↔ 0 < x ∧ x < Δ` (proved); 2 sorry (`riemannZeta (-2) = 0`, `riemannZeta (-4) = 0`).

**(c)** inventory F1–F7: Bloch-length transforms work on deep 1-D chains, fail in 2-D (16–21/30 S3 qubits have |r_χ| < |z_exact|); G2_v9 = z·|r|^½ after a half-step (591/600). The norm-vs-componentwise distinction is exactly "nullify |r|" vs "nullify z"; both hard variants were killed in the emulator (map §3).

### 1.20 Entropy H_N

**(a)** The compilation (§1.2) claims "Shannon entropy H is a strict special case of a nullification-aware entropy H_N" and "formally verified in Lean". **There is no H_N in the corpus.** Grep for `shannon|nullification.aware|H_N\b|entropy_N` finds only: `EntropyClass` (a renamed `NullClass`), hardware constants (`ENTROPY_V6 := 821` etc.), `entropy_critical := 110 -- ln(3)×100`, and `effective_entropy (n_reservoir threshold : Nat) : Nat := n_reservoir / threshold` (BlackHole, def-only). The "entropy below 0.9 ⇒ structure" rule is listed in the compilation as fit on disputed data. The one executable entropy→class map is `Photonic_Isolation_Grid.lean` `def entropy_to_class (e : Nat) : EnergyClass := if e < 750 then zero else if e < 900 then reservoir else observable` (entropy ×1000; hardware numbers `ENTROPY_NULL := 719`, `ENTROPY_VLASOV := 884`; every theorem about it is `native_decide` on those literals). Its ordering is the *reverse* of N's — low entropy ↦ `zero` ("heavy projection occurred"), high ↦ `observable` — and it is a lookup table on a measured number, not a function of N or R; the photon-isolation thread it belongs to is the one the compilation flags as provisional.

**(c)** inventory F3: `z·(1 − S(ρ_q))` with S the binary entropy of (1+|r|)/2 — a *proposed* H_N on Bloch vectors; S2 −0.121, S3 +0.037, G1 +0.297; fails the kill criterion.

### 1.21 Measurement as nullification (quantum layer)

**(a)** `Quantum_Nullification_Aristotle.lean`: 32 theorems, **25 sorry** (never closed); `measure_nullification_correspondence (Δ) (alpha_val) (h : alpha_val < Δ) : N Δ alpha_val = 0 := by sorry`; `classify_qubit (ψ) (entangled : Bool) : QuantumClass` (|0⟩ entangled ↦ `operational` [0.0e]) — def-only; `quantum_conservation` is `rfl` on an identity. The "entanglement implements R" claim has no theorem. The compilation flags the photon-isolation (QED) results as provisional; the Lean side of that thread is numeric constants.

### 1.22 Reals, continuity, limits (Phase IV), pre-continua

**(a)** `Nullification_Phase4_Reals__1_.lean` is Float with `#eval` only: discontinuity at ±Δ, Lipschitz within classes, `integrate` rectangle rule — **no theorems**. The Robinson file notes `N(Δ→0) ≠ st()` (limit is the identity). `Nullification_PreContinua_Fixed__1_.lean`: `refineResolution` (def), `precontinuum_conservation` and `refinement_preserves` (proved, trivial).

### 1.23 Solver code (Joey's `nullification_*.py`, quimb notebook)

**(a)** `nullification_mps.py` `NullificationMPS.apply_two`: after SVD, `threshold = 1e-10 * S[0]`, `keep = max(2, min(#S > threshold, chi_max))`, `self.remainder += sqrt(Σ S[keep:]²)`. **This is N on the Schmidt spectrum with a relative (dilation-covariant) Δ, and R accumulated as a scalar.** R is logged, never re-used.
`nullification_holographic.py` `apply_two`: three-class truncation — `one_threshold = 0.01 * S_max` ([1]), `zero_threshold = 1e-14 * S_max` ([0]), `n_remainder` between; `keep = min(max(n_one + n_remainder // 2, 2), chi_max, len(S))` (keep all [1], half the [0.0e], no [0]); `HolographicNullification.absorb_remainder` keeps `boundary_dim` modes of the discarded block (second-level N on R) and `get_correction_factor = exp(-0.01 * total_remainder)` multiplies the peak probability (an ad-hoc shrinkage by R). These are the only executable three-class algorithms in the corpus. `nullification_fast.py` / `nullification_parallel.py` are path samplers (no N). The notebook is a plain quimb `Circuit.sample` run; its only MNF content is the title.
**(c)** BlueQubit's `mps.cpu` does the same truncation with absolute χ; the inventory's B1 is the "remainder proxy" because the platform does not report the discarded weight.

---

## 2. The OTOC map's pre-registered operations (not Lean) — pointers only

`explore/MNF_x_OTOC_map.md` §3–4 defines `mnfZ(D) = N(D, z)`, `mnfR(D) = z·[|r| ≥ D]`, `soft(D) = z·min(1, |r|/D)`, Richardson in χ, Bloch-length escalation order, and the kill criterion (≥ +0.005 corr² on two of S1–S3, never negative on the third). Results: hard-z/hard-r **killed**, Richardson **killed as default**, soft ≤ ±0.01 (noise). `inventory.md` tests 25 further mappings (A1–H); the ones that "did work" (A1 light cone, A3 zero-draw = [0.0e], D1/D2 non-distributivity as fragmentation, F6 half-step·|r|^½) are all either the projector itself or non-distributivity. Nothing from §1.10–1.17 (probes, leveling, ejection, toroid, wormhole, NLoS) has a data counterpart, and none is mappable to MPS/PP data (inventory "Not mappable").

---

## 3. Where INJECTION would sit

The corpus never defines injection. The word occurs only as "degeneracy injection (224 CX, state-copying CNOTs)" in `EmpiricalBridge.lean:130` (a hardware circuit, axiomatised as `degeneracy_kills_gap`) and as Mathlib's `Function.Injective`/`injective` (output89, QI_v3, MdBatch5). Below: (a) what the corpus says about the reverse direction, (b) the formal slot.

### 3.1 (a) The reverse direction [1] → [0.0e] in the corpus

| mechanism | where | status | what it actually does |
|---|---|---|---|
| **Raise the threshold** | `output97` `reclassification_by_scale`, `IsInShell`, `N_disagrees_across_scales`, `threshold_ordering_creates_class_shift` | proved | x with Δ₁ ≤ \|x\| < Δ₂ is [1] at Δ₁ and [0.0e] at Δ₂: `nullify Δ₁ x = x ∧ nullify Δ₂ x = 0 ∧ remainder Δ₂ x = x`. **This is the only proved way observable content enters a reservoir: change Δ, not x.** |
| **Lower the threshold** (the inverse, i.e. ejection by refinement) | `PreContinua` `refineResolution` (Δ/2), `refinement_preserves` | def / trivial | [0.0e] at Δ becomes [1] at Δ' ≤ \|x\| |
| State cycle [1] → [0.0e] | `Complete_Nullification_Framework` `evolve quantified = nullified`; Ramanujan `next_state quantified = infinitesimal`, `transition_energy quantified infinitesimal = 0 -- releases` | proved on enums | relabelling of a two/three-element type; no value moves |
| Infall into the reservoir | `BlackHole_Singularity_Resolution` comments ("Infalling matter → adds to [0.0e] pool (past)"), Grand_Unified Part VIII | prose only | no definition |
| Adding content to the pool | `cycleStep` (`s.remainder + input`), `sumR`, `sumRemainders`, `poolRemainders`, `accumulate`, `pool_sum`, `compose_real a b c := a + b + c` | def-only / list-sum theorems | the pool is `Σ R`; "inject y" = cons y onto the list |
| Absorbing a spike without ejection | `output98` `half_threshold_absorbs_spike (h_half : μ < Δ/2) (h_spike_bound : ε < Δ/2 - μ) : μ + ε < Δ`, `zone_returns_to_reservoir_after_spike (h_absorbed : μ + ε < Δ) : classify_F Δ (μ + ε) = reservoir`, `safety_margin_half_threshold` | proved (linarith) | **the closest formal "injection-safety" theorem**: a reservoir value μ accepts an increment ε and stays [0.0e] iff μ + ε < Δ; the Δ/2 rule guarantees a margin ≥ Δ/2 |
| Splitting a value into sub-threshold pieces | Batch12 partition theorems (`isPartition`, `sumR Δ parts ≥ Δ` for parts < Δ) | proved on literals | an observable n re-partitioned into pieces each < Δ is a pool that still sums to n: **injection by re-partition** (this is what pauli-path fragmentation does to a path weight — inventory D2) |
| R stores losslessly | `remainder_stores_intact`, `subthreshold_content_recoverable`, `remainder_in_evanescent` | proved | guarantees that whatever is put below Δ is recoverable via R |

### 3.2 (b) Proposed formal slot (nothing below is in the corpus)

```lean
-- Injection of y into the reservoir value x at threshold Δ (two-sided real operator):
def inject (Δ : ℝ) (x y : ℝ) : ℝ := remainder Δ (x + y)       -- the part that stays below Δ
def eject  (Δ : ℝ) (x y : ℝ) : ℝ := nullify   Δ (x + y)       -- the part that crosses
theorem inject_eject_conservation : inject Δ x y + eject Δ x y = x + y           -- = nullify_conservation (x+y)
theorem inject_stays_reservoir (h : |x + y| < Δ) : inject Δ x y = x + y ∧ eject Δ x y = 0     -- = remainder_stores_intact
theorem inject_ejects (h : |x + y| ≥ Δ) : inject Δ x y = 0 ∧ eject Δ x y = x + y            -- = nullify_routes_intact
theorem inject_not_additive : ∃ Δ x y, eject Δ x y ≠ nullify Δ x + nullify Δ y                -- = not_linear
-- Injection by dilation (content fixed, scale moved):
theorem inject_by_scale (h₁ : |x| ≥ Δ₁) (h₂ : |x| < Δ₂) : nullify Δ₁ x = x ∧ remainder Δ₂ x = x   -- = reclassification_by_scale
theorem dilation_covariance (hc : 0 < c) : nullify (c*Δ) (c*x) = c * nullify Δ x
```
Reading: in the two-sided algebra, injection is **the sum inside non-distributivity** (`N(x+y)` vs `N x + N y`), and `cycleStep` is already the inject–eject cycle with state. The three facts the corpus has proved about it are conservation, the two routing lemmas, and the half-threshold absorption margin. What is **missing** and would be new: any statement with *time* (a sequence x_t with injections and ejections; `unique_collapse_point` is the only time-indexed theorem and it is one-way), any *signed* injection theorem (injecting −ε into a +0.0e pool: by `mixed_can_cancel` it can produce a false ground — this is the Type-B hazard; `one_sided_sum_zero_iff` says one-signed injection cannot), and anything about injection *across qubits/sites* (the map's "pool across neighbours", inventory D5, untested).

### 3.3 (c) What the data already said about injection, in these words

STATUS 08:10 (Joey): "the 'nullification setting' alpha … is regime-dependent … G4's magnitudes are sub-resolution residue → compression and nullification win". Inventory D2: fragmentation = a path weight re-partitioned over more Pauli strings, each falling under the platform's threshold piece by piece — injection of [1] content into [0.0e] by re-partition, 9/9 pairs. The sign gate (G4_v7, +70) is `is_degenerate`-filtering on the pool; G4_v8/v9 showed that further nullification (single-run IDs → 0; sign-only) loses — the pool's magnitudes are information. No MNF operation beyond N, R-as-store, sum, and the signed coherence test has been needed to explain any score.

---

## 4. Inconsistencies between files (numbered, with evidence)

1. **ℕ one-sided vs ℝ/ℤ two-sided.** 57 files use `x ≥ Δ` on ℕ, 40 use `|x| ≥ Δ`. Theorems proved on ℕ and quoted as "the" properties (threshold monotonicity, `just_below_threshold`, `R_at_threshold`) do not all transfer; see §1.3 for the one that fails on ℝ.
2. **One-sided real operators.** `MdBatch2.lean:50`, `MdBatch4.lean`, `MdBatch7.lean:97` define N on ℝ **without** |·| (`if E < Δ then 0 else E`); `MdBatch1.lean:55` defines `N (Δ E : ℝ) : ℝ := E` (identity). These contradict Core for negative inputs / everywhere.
3. **x ≥ Δ is observable at the boundary** (`at_threshold : N Δ Δ = Δ`, `ejection_state_is_observable : IsObservable Δ Δ`) while the prose repeatedly says "[0.0e] : 0 < |x| < Δ" and "x → Δ ejects" — consistent, but note the strict/non-strict asymmetry: the reservoir is open, the observable class closed. The Bloch file flips it (`nsq >= purityThresholdSq`) while the map uses "|r| < Δ nullified".
4. **R as `x − N` vs explicit branch** (Core/Complete_v4/EnergyFlow_v4 vs all others) — equal; harmless.
5. **Δ/2 probe vs Δ threshold.** RH: band (0,1), midpoint ½, gap ½ ⇒ squeeze works. Wormhole: band (0,Δ), midpoint Δ/2, gap Δ ⇒ the "leveling" theorems only bound (`|probe| < Δ/2`), they do not level; `IsEjectionThreshold x = Δ` sits at the *edge* of the band while `north_probe_zero_iff` pins the *centre*. Two different points are both called the ejection/leveling locus. (§1.10–1.12)
6. **Name collisions on "τ/2".** `tau_half_real`/`tau_half_nat` (squeeze at ½) vs `tau_half_is_pi`/`tau_eject` (angle π). Unrelated statements with one name; Batch17's comment "The zero exits through Re(s) = 1/2 = τ/4... wait" shows the confusion in-source.
7. **Three unrelated "ejection"s** (§1.12 i–iii) connected only by comments.
8. **Leveling import missing.** `LevelingTheorem_PaperFacing.lean` imports `lean_files.LevelingTheorem`; no such file in the folder. `HPContext.lean` imports `lean_files.Batch14_MasterEnforcement` and says "N … (re-export from Batch14)" but Batch14 defines N on ℕ and HPContext redefines it on ℝ — the import would clash or be unused. The paper cites `MinimalAxiomReduction.lean` and `SturmLiouvilleSimplicity.lean`; neither is in the folder (the content is in `pair3_*`, `output71_minimal_axiom.lean`, `sturm_liouville_*`).
9. **Superfluous hypotheses.** Every ℝ `idempotent` carries `0 ≤ Δ`/`0 < Δ`; idempotence holds for all Δ (N 0 = 0 in both branches). `master_enforcement` carries `hΔ : Δ > 0` unused; HPContext's ℝ copy drops it.
10. **"N ≡ st()" (Batch11) is `rfl`** because `standard_part` is defined by the same formula; `Nullification_Robinson_Correspondence.lean` and output97 say the opposite (N is not a homomorphism, not isomorphic to st). The AFM v7 appendix adopts the corrected reading; the compilation's §1.2 ("formally verified") does not say which.
11. **Information.** Batch14 defines `LosesInformation f := ∃ x, x > 0 ∧ f x = 0`, under which N loses information; the prose claims the opposite; the definitions are unused.
12. **Degenerate-zero instances false as written**: `xi_typeA_degenerate` (Batch4_2; 192 < 246), `xi_minus_neg_reservoir`/`xi_c_plus_pos_reservoir`/`xi_pair_is_degenerate_zero`/`three_sector_gap_confirmation` (Batch4_1; |±1| ≥ 1 is observable) — each later file documents the previous one's failure. Batch4_1 and Batch4_2 as on disk contain `decide`/`simp` proofs of false statements and would not compile.
13. **Aristotle negations left in place**: `collapse_condition`, `post_collapse_is_observable` (Batch13_TCO3_Collapse), `messina_ono_concrete` (Batch12), `hole_count_is_topological_invariant` (Batch17), `prior_proposals_hit_barrier` (wormhole_3 v1), `bounded_probes_imply_bypass` (Set3_2 `exact?` stall). The corrected versions exist (Batch13.lean, Theorem120_Fix (still sorry), Batch17_1, Set3_1, Set4).
14. **True-stubs presented as theorems**: `GeodesicFollowsGeometry := True`; `NLoSDualityCorrespondence` (5 × True), `all_five_correspondences := { … := trivial }`; output90/93/94 records likewise; `ZeroDensityControl` has three bare `Prop` fields.
15. **Axioms that are not axioms**: `ibm_mass_gap_positive : (192:ℝ)/100 > 0`; `aristotle_stress_test_synthesis` re-axiomatises `conservation`, `idempotent`, `master_enforcement`; `EmpiricalBridge` axiomatises hardware results; `func_eq_deriv` (output86) and `st_is_RingFlux_on_finite` (nsa_bridge_part2) are genuine unproved assumptions.
16. **Header claims vs content**: output86 "Zero sorry. Zero exact?." (1 sorry, 1 axiom); `full_cascade_loop_breaker` "two sorry markers" (six sorry terms on four lines); output92 "Zero sorry targets" (true — the one match is prose); AFM v7 "zero-sorry" refers to the paper's 82-file subset, not this 301-file folder.
17. **Encoding.** `Batch1/2/3_*_v2.lean`, `Batch14_MasterEnforcement.lean`, `output56_signed_nullification_v2.lean`, `output57_*_v2.lean`, `PathD_Contrapositive.lean` are stored UTF-8-as-cp1252 (`Î”`, `â‰¥`); they do not parse as on disk. Their non-v2 twins are clean.
18. **Ten re-inventions of the three-class type** with different constructor names (§0); `classify` on ℕ puts `x = 0` first, so `classify 0 0 = zero` while `N 0 0 = 0 = x` is a fixed point of the observable branch — this is exactly the `Δ = 0` corner Aristotle used to negate `post_collapse_is_observable`.
19. **Nat subtraction.** `Axis3_MultiplicityDev order := order - 1` gives 0 for order 0 and 1 alike (`master_sphere_theorem` has to carry `order = 1 ∨ order = 0`); `mult_deviation_nat`; Ramanujan `present_future_ratio` sorry "Requires careful Nat division handling".
20. **Scale of Δ on the Bloch sphere**: Bloch file thresholds |r|² (`Δsq`), the map says "x = |r| (or |r|², the fork noted in mnf_qexp RESEARCH_NOTES §2.1), Δ = ½"; inventory F3 tests both.

---

## 5. Proof-status census of the key files

Counts by hand where the grep heuristic is unreliable. "raw" = lines containing the string `sorry`; "proof" = `sorry` terms in proof positions; "axiom" = `axiom` declarations; "exact?" = search-tactic proofs.

| file | theorems | raw sorry | proof sorry | axiom | exact? | note |
|---|---|---|---|---|---|---|
| Nullification_Core.lean | 8 | 0 | 0 | 0 | 0 | ℝ, Mathlib; the reference core |
| Nullification_Geometry.lean | 2 | 0 | 0 | 0 | 0 | rest is `#eval` |
| Nullification_Bloch.lean | 0 | 0 | 0 | 0 | 0 | `#eval` only |
| Batch1_Classification(.lean / _aristotle / _v2) | 10 | 10 / 0 / 0 | 10 / 0 / 0 | 0 | 0 | v2 is mojibake |
| Batch2_Monotonicity(.lean / _aristotle / _v2) | 10 | 10 / 0 / 0 | 10 / 0 / 0 | 0 | 0 | |
| Batch3_Distributivity(.lean / _aristotle / _v2) | 10 | 10 / 0 / 0 | 10 / 0 / 0 | 0 | 1 (`six_nullified`) | |
| Batch4_1_XiBaryon_SignedProbe-1 | 18 | 1 | 0 | 1 | 0 | 5 theorems false as written |
| Batch4_2_DegenerateZeroMechanisms-1 | 16 | 1 | 0 | 0 | 0 | 1 theorem false as written |
| Batch4_3_TriangleDegenerateZero | 16 | 1 | 0 | 0 | 0 | |
| Batch5_Image_aristotle | 10 | 0 | 0 | 0 | 1 | |
| Batch12_PartitionPower_Aristotle(_aristotle) | 10 / 11 | 10 / 1 | 10 / 1 | 0 | 0 | `messina_ono_concrete` negated |
| Batch13_TCO3_Collapse / Batch13 (Aristotle) | 10 / 10 | 8 / 0 | 8 / 0 | 0 | 0 | 2 negated, 2 fixed with extra hyp. |
| Batch14_Information_Enforcement / _MasterEnforcement | 12 / 11 | 0 | 0 | 0 | 0 | second is mojibake |
| Batch15_ThreeDSphere-1 | 24 | 3 | 0 | 0 | 0 | |
| Batch16_ZeroZeroE_Field-1 | 28 | 4 | 2 | 0 | 0 | ζ(−2)=0, ζ(−4)=0 |
| Batch17_ToroidNullification / batch17 | 26 / 23 | 5 / 0 | 3 / 0 | 0 | 0 / 1 | Aristotle omitted 3 |
| Batch17_1_TopologicalCorrection | 8 | 1 | 0 | 0 | 0 | |
| LevelingTheorem_PaperFacing | 5 | 0 | 0 | 0 | 0 | missing import |
| pair1 / pair2 / pair3 / pair4 _CONTENT | 3 / 3 / 6 / 1 | 0 | 0 | 0 | 0 | STATEMENT twins are `by sorry` by design (2/3/6/1) |
| output56_signed_nullification | 35 | 0 | 0 | 0 | 0 | |
| output57_signed_multiplicity | 19 | 0 | 0 | 0 | 0 | 4 named hypotheses |
| output71_minimal_axiom | 20 | 0 | 0 | 0 | 0 | 2 named hypotheses |
| output72_master_theorem | 16 | 0 | 0 | 0 | 0 | |
| output86_pole_probe-1 | 19 | 2 | 1 | 1 | 1 | |
| output89_nlos_projection_duality | 41 | 0 | 0 | 0 | 0 | 5 True-fields |
| output92_signed_depth_multiplexing | 41 | 1 | 0 | 0 | 0 | |
| output97_nsa_comparison-1 | 25 | 1 | 0 | 0 | 1 (merged copy: closed) | |
| output98_multizone_optimization-1 | 25 | 1 | 0 | 0 | 0 | |
| wormhole_1 / 2 / 3 / 3_v2 / 4 | 10 / 11 / 15 / 24 / 13 | 0 | 0 | 0 | 0 / 0 / 0 / 0 / 3 | wormhole_3 v1 has 1 false theorem |
| MNFmeetsDavisSet1 / 2 / 3_1 / 3_2 / 4 | 7 / 11 / 15 / 23 / 19 | 0 | 0 | 0 | 0 / 0 / 0 / 1 / 1 | |
| mnf_wormhole_nsa_merged | 71 | 0 | 0 | 0 | 0 | |
| full_cascade_loop_breaker | 15 | 14 | 4 lines / 6 terms | 0 | 0 | |
| HPContext | 2 | 0 | 0 | 0 | 0 | the named open hypothesis is a `structure` |
| MNF_Bridge78 (Downloads) | ~45 | 0 | 0 | 0 | 0 | one hypothesis `ZeroFreeRightOf (7/8)` |
| Complete_Nullification_Framework | 10 | 0 | 0 | 0 | 0 | 10 native_decide |
| Grand_Unified_Nullification__2_ | 38 | 0 | 0 | 0 | 0 | 61 native_decide on literals |
| Nullification_Full_Framework | 5 | 0 | 0 | 0 | 0 | |
| Nullification_Robinson_Correspondence / Phase3 / Phase4 | 0 | 0 | 0 | 0 | 0 | Float/`#eval` |
| batch11_nsa_equivalence_aristotle | 10 | 0 | 0 | 0 | 0 | tautological core |
| Quantum_Nullification_Aristotle | 32 | 25 | 25 | 0 | 0 | never closed |
| Nullification_Aristotle_Extension(_aristotle) | 37 | 28 / 28 | 26 / 26 | 0 | 0 | Aristotle copy unchanged |
| Nullification_EnergyFlow | 12 | 3 | 3 | 0 | 0 | |
| BlackHole_Singularity_Resolution | 10 | 0 | 0 | 0 | 0 | 12 native_decide |
| Ramanujan_Temporal_MassGap__1_ | 16 | 1 | 1 | 0 | 0 | |
| tco3_collapse_master_phone(_v2) | — | 2 / 2 | 2 / 2 | 0 | 0 / 1 | |

Corpus-wide: 352 raw `sorry` lines in 73 files; ≈243 proof-position by regex (undercounts tuples); `axiom` declarations in 29 files (≈100 lines, incl. `aristotle_stress_test_synthesis` re-axiomatising proved results); `native_decide` ~1500 uses, almost all on numeric literals.

---

## 6. Summary of what is operational beyond N (one line each, honest status)

| operation | formal object | best status | relation to N, R |
|---|---|---|---|
| remainder / conservation | `remainder`, `N + R = id` | proved everywhere | defines R |
| idempotence, image, fixed points | `fixed_point_iff`, `in_image_N`, `agreement_locus_subthreshold` | proved | N is a retraction onto {0} ∪ {\|x\| ≥ Δ} |
| composition laws | `R_comp_N = 0`, `N_comp_R = 0` | proved (ℕ) | N, R annihilate each other |
| monotonicity | `N_monotone`, `threshold_monotone` | proved (ℕ); ℝ Δ-version false for x<0 | — |
| dilation covariance | none | **absent**; proposed, trivial | only x/Δ |
| spectral gap / enforcement | `spectral_gap`, `master_enforcement`, `SpectralGapProperty (Set.range N)` | proved | the gap is N's definition on its range |
| non-distributivity / pool | `not_linear`, `accumulation_crosses_threshold`, `sumR`, `pool_threshold_exists` | proved | `N ∘ Σ ≠ Σ ∘ N`; the one non-trivial law |
| pool with state (inject–eject cycle) | `cycleStep`, `evaporation_step`, `hawking_emission` | def-only | sum, then N; reservoir decremented only in `evaporation_step` |
| partition vs power | Batch12 (literals) | proved / 1 negated | additive pools cross gradually, powers jump |
| degenerate zeros A/B/C/Unified | `IsDegenerateZero_*` | defs; instances corrected twice | A = non-distributivity; B = cancellation in [1]; C = A with three parts |
| signed classes, coherent/degenerate pools | `SignedNullClass`, `SignedTriple.is_coherent`, `one_sided_sum_zero_iff` | proved | sign of R-values; sums |
| probes | `NorthProbe Δ x = x − Δ/2`, `Dev` | proved (affine identities) | no threshold content; recentring |
| leveling | `leveling_theorem` (RH), `tau_half_real`, Bridge78 `tau_threshold` | proved | N-free squeeze lemma |
| ejection | `IsEjectionThreshold x = Δ`, `EjectionPoint = π`, `tau_eject` | defs; theorems are definitional | boundary predicate, not an operator |
| cascades | `IsConfinedCascade`, `unique_collapse_point` | proved | N applied termwise; one time-indexed theorem |
| toroid / protection | `hole_count ≥ 1` | proved on records | no topology |
| wormhole throat / bypass | `IsThroatPoint`, `spectral_incompatibility` | proved | three reservoir scalars; class disjointness |
| NLoS duality | `NLoSContext` (iso), `Evanescent/PropagatingSpace` | proved / True-stubs | H is unrelated to N in the file |
| NSA routing vs forgetting, shells | `reclassification_by_scale`, `IsInShell`, `routing_functor_theorem` | proved | **the only proved [1]→[0.0e] mechanism: move Δ** |
| geometry: componentwise vs norm | `nullifyComponentwise`, `nullifyNorm` | conservation proved; difference `#eval` | which scalar gets thresholded |
| Bloch / sphere | `nullifyBloch`, `sphereClassify` | def-only / relabelled classify | — |
| entropy H_N | none | **absent** | — |
| measurement | `measure_nullification_correspondence` | sorry (25 in file) | — |
| injection | none | **absent**; slot in §3.2; ingredients proved (`remainder_stores_intact`, `half_threshold_absorbs_spike`, `reclassification_by_scale`) | the sum in non-distributivity |

---

## 7. Files and provenance

- Catalogue: `C:/Users/jmess/otoc_audit/mnf2_formal/catalogue.md` (this file).
- Extracted text used for the paper/docx quotes: `C:/Users/jmess/otoc_audit/mnf2_formal/_extract/afm_v7.txt`, `…/paper.txt`, `…/spectral_gap_docx.txt`.
- Corpus read-only: `C:/Users/jmess/Downloads/nullification_cascade_lean/files/` (301 files), `C:/Users/jmess/Downloads/MNF_Bridge78.lean`, `C:/Users/jmess/Downloads/mnf_wormhole_nsa_merged.lean`, `C:/Users/jmess/Downloads/MNF_Complete_Compilation_and_Corrections.md`, `C:/Users/jmess/Downloads/otoc_hack/otoc_hack/explore/MNF_x_OTOC_map.md`, `C:/Users/jmess/otoc_audit/mnf_inventory/inventory.md`, `C:/Users/jmess/Downloads/otoc_hack/otoc_hack/STATUS.md`, `…/ALL_NOTES.md`, `C:/Users/jmess/Downloads/nullification_{mps,fast,holographic,parallel}.py`, `C:/Users/jmess/Downloads/Nullification_Quimb_Solver.ipynb`, the two PDFs and the docx.
- Compilation's own flags honoured: V6–V13 photon isolation provisional (Correction 2), Grover disproven (3), 6√2·Λ_QCD abandoned (4), RH/Simple Zeros conditional (5). None of those threads contributes an operation to this catalogue beyond the numeric constants noted.
