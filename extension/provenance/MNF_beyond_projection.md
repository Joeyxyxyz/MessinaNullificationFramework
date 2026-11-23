# MNF beyond projection — injection, ejection, cascades, residues, soft gates

> **Corrections applied 2026-11-03 after the adversarial check** (`mnf2_verify/checks.md`): the G3 fragmentation tally is 13/13 distinct
> variant pairs (not 23/23, which counted identical repeats) and G4 2/4; the "unique never-wrong rule" claim about the sign gate is withdrawn
> (abstention is forced, the common-sign half is not safe, the gate is empirical); the Type-A window medians are 1.62 octaves / 3.07 over the
> 21 window IDs; the S3 q17 worked example is the platform ladder, now labelled, with the local-ladder numbers beside it; "in-process is
> strictly more confining" is downgraded to an empirical regularity with a counterexample; Tobin (1958), not "Tobit"; the Lean sketch gained
> `open scoped Classical` so `eject_sub_nullify` elaborates. Every other number and every proof-status claim was reproduced by the check.

**Synthesis for Joey, 2026-11-03.** Folder `C:/Users/jmess/otoc_audit/mnf2_synth/` (this file, `MNF_Injection_Ejection.lean`, `check_synth.py`).
It consolidates four reports written for the request *"explore beyond projection operations with the Nullification framework. explore
Injection & ejection. and much more."*:

| report | what it did | where |
|---|---|---|
| formal corpus map | read all 301 Lean files + PDFs/docx/solver code; catalogued every operation beyond N with its proof status | `C:/Users/jmess/otoc_audit/mnf2_formal/catalogue.md` |
| operator algebra | designed E, J, I_k, ν, δ*, residue, gates; prose proofs; numpy property tests | `C:/Users/jmess/otoc_audit/mnf2_algebra/algebra.md`, `mnf_ops.py` |
| numerical lab | measured cascades on the hackathon data (G3/G4 platform draws, S3 local ladders with truth, MPS χ-ladders) | `C:/Users/jmess/otoc_audit/mnf2_lab/results.md` |
| literature placement | standard name and reference for each operation; what MNF adds | `C:/Users/jmess/otoc_audit/mnf2_lit/placement.md` |

**How to read every claim.** Three tags, used on every line that matters:
**(a) corpus** — defined or proved in the Lean corpus. "Proved" means a complete, non-placeholder proof text is present in the file; there is
**no Lean toolchain on this machine**, so nothing was compiled. Where a file has `sorry`, an `axiom`, a `True`-stub or a statement Aristotle
negated, it says so. **(b) proposed** — designed in this exploration; prose proofs, numpy tests (`python -I mnf_ops.py`: seeds 0, 7, 123,
2000–3000 random trials each, all pass, re-run by this step on 2026-11-03), Lean statements **unverified**. **(c) data** — observed on the
BlueQubit OTOC hackathon files (Oct 24–25, 2026); every number carries its n. No BlueQubit calls were made in this exploration.

Plain-language rule: the corpus core is a scalar hard threshold; the extension is a small algebra around it; the data say which parts of
that algebra did work on real simulations and which did not. Nothing below is presented as more than that.

---

## 0. Summary

1. **The corpus, beyond the projector N, formally contains:** the remainder R with N + R = id; idempotence and the image/fixed-point
   characterisation; the spectral gap on the range of N; monotonicity (proved on ℕ only); **non-distributivity / pool accumulation** (the one
   non-trivial law); signed classes ±0.0e with coherent/degenerate pools; the affine probes x − Δ/2; an N-free leveling lemma; cascades as
   termwise N; degenerate zeros of Type A (= non-distributivity with the sum hidden) and Type B (= cancellation inside [1]);
   partition-vs-power on literals; reclassification by scale (the only proved way observable content enters a reservoir: move Δ, not x);
   a half-threshold absorption margin; and one stateful inject-then-nullify cycle (`cycleStep`, definition only). **Ejection** exists only as the
   boundary predicate `x = Δ` (probe reads Δ/2) plus an angle π on a toroid; it is never an operator. **Injection is undefined.** Dilation
   covariance ("only x/Δ matters") and the "nullification-aware entropy H_N" have no Lean counterpart. (§1)
2. **The extension (proposed).** Injection cannot be a content-conserving map of values (the only such map is the identity), so it lives on
   *representations* ρ = (p_1,…,p_k) of a value x = Σp_i: injection is **fragmentation** I_k x = (x/k,…,x/k), the simulators' piecewise reading
   is ν_Δ(ρ) = Σ N(Δ,p_i), and the exact identity **ν_Δ ∘ I_k = N_{kΔ}** says injection is threshold dilation. **Ejection** is the operator
   E(Δ,x) = sgn(x)·max(|x|,Δ): N and E are the two idempotent retractions of ℝ onto the gapped set G_Δ = {0} ∪ {|x| ≥ Δ}, floor and ceiling,
   with E ⊣ incl ⊣ N on the half-line. The **deficit** J = E − id is the reflection of the reservoir about its midpoint and generates N, R, E
   (J∘J = R, J³ = J); the corpus probe pair is J's action (NorthProbe∘J = SouthProbe). A **threshold ladder** is a family of readings of one
   representation, not an iterated operator (N_a∘N_b = N_max); its ejection threshold δ*(ρ) = sup{Δ : ν_Δ(ρ) ≠ 0} obeys a refinement
   theorem for same-sign pieces and nothing for mixed-sign ones. The **signed cancellation residue** res_Δ(ρ) = ν_Δ(ρ) − N(Δ, Σp_i) explains the
   sign gate: abstaining on a sign contradiction is forced (any rule that outputs a sign on a contradictory multiset is wrong on some value),
   while keeping a coherent common sign can still be wrong (every multiset of readings is realisable from every value), so the gate is
   minimax and its standing is empirical, not a certificate; the only reading-only rule that never asserts a wrong sign is the constant 0. **Soft** nullification z·g(w) is a gated operator; idempotence and
   pass-or-kill hold iff the gate is hard. (§2)
3. **What the data showed (numbers in §3).** Fragmentation is real and has one mechanism everywhere: a larger expansion of the same unitary
   reads 0 or a shrunken/sign-flipped residue where the compact one reads the value (G3 platform 9/9 same-threshold pairs; 13/13 distinct variant pairs
   with the zero draw from the larger expansion — 23 draws counting identical repeats; S3 local 26/32, 22/28, 30/37); selecting the compact representation and never averaging in fragmented or
   exact-zero draws is what took G3 373 → 430 (averaging them lost 47). The sign gate took G4 48 → 118; the stricter and looser alternatives
   scored 56 and 54. The ejection threshold of a real cascade is emergent: on S3 it tracks |truth| with slope 0.65 and sits ~12× below it, the
   reading at ejection is ~0.4 of the final value with the final sign (0.39 n 28 local; 0.36 n 10 and 0.36 n 5 platform) — never the
   scalar probe's Δ/2 — and in-process truncation was more confining than nullifying the final pieces on every ID tested (25/25; an empirical regularity,
   not a general theorem — a two-coordinate counterexample exists, §2.4). The soft gate
   z·|r|^½ paid on a 1-D chain (G2 549 → 591) and fails in 2-D at χ ≤ 32, because the Bloch length is a contracting witness only in 1-D
   (S2 contraction 0.20, ρ +0.92, n 12; S3 ρ −0.06, n 29).
4. **Literature (§4).** Every operation has a standard name (hard thresholding, residual, censoring, block thresholding, truncate-after-merge,
   closure/kernel operators, first passage, sign consistency, firm shrinkage). What is Joey's: the one vocabulary across χ-, δ- and Bloch
   truncations; the fragmentation/compaction reading of transpilation variants and the fewest-`max_paulis` rule; "a contradicted sign is a
   cancellation residue, so abstain"; the exact-zero-as-non-detect rule imported into circuit simulation; the regime-dependent α.
5. **Lean (§5).** `MNF_Injection_Ejection.lean` holds 31 definitions and 56 theorem statements: 18 carry a complete proof attempt (short
   definitional or case-split arguments), 38 carry `sorry` with the intended argument in a comment. Unverified. **Open questions and the next
   experiments are in §6.**

---

## 1. The operator algebra as it stands in the corpus (with proof status)

### 1.1 The three-line core

```lean
-- Nullification_Core.lean (ℝ, Mathlib; 8 theorems, 0 sorry)
def nullify (Δ : ℝ) (x : ℝ) : ℝ := if |x| ≥ Δ then x else 0
def remainder (Δ : ℝ) (x : ℝ) : ℝ := x - nullify Δ x
def classify (Δ : ℝ) (x : ℝ) : NullClass := if x = 0 then zero else if |x| ≥ Δ then observable else nullified
```

Classes: [0] x = 0 (true zero); [0.0e] 0 < |x| < Δ (confined reservoir, open interval); [1] |x| ≥ Δ (observable, closed at Δ). The corpus
re-declares this operator about 100 times (57 files one-sided `x ≥ Δ` on ℕ, 40 two-sided `|x| ≥ Δ` on ℝ/ℤ, 3 one-sided on ℝ without |·|, and
`MdBatch1.lean:55` where `N (Δ E : ℝ) := E` is the identity). Nothing imports anything, so every law is re-proved per file; theorems proved
on ℕ do not all transfer to the two-sided real operator (§1.2, monotonicity). (a)

### 1.2 Laws of the core, with status

| law | statement | status | where |
|---|---|---|---|
| conservation | N + R = id | proved (definitional) | Core `conservation`; everywhere |
| idempotence | N∘N = N | proved; every ℝ copy carries a superfluous `0 ≤ Δ` | Core `idempotent` |
| image / fixed points | N x = x ↔ x = 0 ∨ \|x\| ≥ Δ; range N = G_Δ | proved (ℕ Batch5; ℝ output97 `nullify_fixed_iff`) | |
| annihilation | R∘N = 0, N∘R = 0 | proved (ℕ) | Batch2 aristotle `R_comp_N`, `N_comp_R` |
| spectral gap | N x = 0 ∨ \|N x\| ≥ Δ; (0,Δ) empty in the range | proved; it is the definition read on the range | Core `spectral_gap`, `gap_empty`; Batch14 `master_enforcement`; HPContext |
| monotonicity in x | x ≤ y → N x ≤ N y | proved on ℕ; holds on ℝ (case check, not written) | Batch2 `N_monotone` |
| monotonicity in Δ | Δ₁ ≤ Δ₂ → N_{Δ₂} x ≤ N_{Δ₁} x | proved on ℕ; **false as stated on ℝ for x < 0** (x = −1, Δ₁ = ½, Δ₂ = 2); correct form \|N_{Δ₂}x\| ≤ \|N_{Δ₁}x\| is written nowhere | Batch2 `threshold_monotone` |
| **non-distributivity** | ∃ x y, N(x+y) ≠ N x + N y (witness Δ/2 + Δ/2) | proved | Core `not_linear`; Batch3 |
| **pool accumulation** | ∀ n ≥ 2 ∃ x, \|x\| < Δ ∧ \|n·x\| ≥ Δ; sumR of sub-threshold list ≥ Δ | proved | Core `accumulation_crosses_threshold`; Batch3 `accumulation_possible`; output88 `pool_threshold_exists`; output92 |
| list conservation | sumN + sumR = sumList | proved **only for `[]`, `[x]`, `[3,12]`**; general statement `sorry` | Batch3 aristotle; Nullification_Aristotle_Extension (26 sorry) |
| sign preservation | \|x\| ≥ Δ → N x = x; R > 0 ↔ x > 0 ∧ \|x\| < Δ | proved | Core `preserves_sign`; output56 `reservoir_sign_pos/neg` |
| dilation covariance | N(cΔ, cx) = c·N(Δ,x), c > 0 | **absent** (the only "scale invariance" theorem, `same_wall_scale_invariance`, concludes `True`) | stated in the OTOC map only |

### 1.3 Beyond the projector: what the corpus has

| object | definition (verbatim or condensed) | status | relation to N, R |
|---|---|---|---|
| signed classes ±0.0e | `SignedNullClass {ground, pos_reservoir, neg_reservoir, observable}`; `signed_classify_int` | proved, 35 theorems, 0 sorry (output56) | sign of R-values; `signed_strictly_finer` |
| coherent / degenerate pools | `SignedTriple.is_coherent := pos_count = 0 ∨ neg_count = 0`; `mixed_can_cancel : ε + ε + (−2ε) = 0`; `coherent_pos_no_cancel`; `one_sided_sum_zero_iff` (output57) | proved | a property of sums of R-values (the pool), not of N; the formal object behind the G4 sign gate |
| probes | `NorthProbe Δ x := x − Δ/2`, `SouthProbe := −(x − Δ/2)`; `probe_balance : N + S = 0`; `north_probe_zero_iff ↔ x = Δ/2`; `wormhole_leveling_north : \|NorthProbe\| < Δ/2` for 0 < x < Δ | proved (affine identities) | no threshold content by themselves; `probe_balance_encodes_conservation` is an ↔ between two always-true statements |
| leveling | `tau_half_real : (∀ x ∈ S, \|x\| < ½) → SpectralGapProperty S ½ → S ⊆ {0}`; Bridge78 `tau_threshold` (general Δ) | proved | N-free squeeze lemma; in the RH setting band (0,1)/gap ½ it levels; in the wormhole transcription band (0,Δ)/gap Δ it only bounds |
| **ejection (predicate)** | `IsEjectionThreshold Δ x := x = Δ`; `ejection_probe_reading : NorthProbe Δ Δ = Δ/2`; `ejection_state_is_observable`; `below_ejection_is_reservoir`; `master_ejection_theorem` | defined, never used in a theorem; companions proved but definitional (wormhole_4, MNFmeetsDavisSet4: 0 sorry; two proofs use `exact?`/odd tactics, the `_fixed`/`_final` restatements avoid them) | a boundary predicate: no x(t), no rate, no removal from the pool |
| ejection (toroid) | `EjectionPoint := π`; `tau_half_is_pi : 2π/2 = π` (ring); `cascade_ejects_at_pi`, `ramanujan_cascade_converges_to_pi` | **sorry** (3 real sorries in Batch17: π₁-invariance, Ramanujan ×2) | an angle; nothing moves |
| cascades | `IsConfinedCascade Δ seq := ∀ n, N Δ (seq n) = 0`; `IsCriticalCascade := confined ∧ seq → Δ`; `confined_cascade_no_blowup : seq n < Δ` | proved (Batch17 §7, sorry-free block) | N termwise; a critical cascade never ejects by definition |
| the one time-indexed theorem | `unique_collapse_point`: a monotone ℕ-sequence from 0 that crosses Δ has a unique first crossing | proved (Batch13 Aristotle copy; original has 8 sorry, two statements negated without extra hypotheses) | one-way; no ejection/injection dynamics |
| degenerate zero Type A | `N Δ x = 0 ∧ N Δ y = 0 ∧ N Δ (x+y) ≠ 0`; `typeA_is_nondistributive` | proved; the headline instance `xi_typeA_degenerate` is false (96+96 = 192 < 246); Batch4_3's corrected form makes z an independent parameter and says nothing about N | non-distributivity with the sum hidden |
| degenerate zero Type B | `\|x\| ≥ Δ ∧ \|y\| ≥ Δ ∧ x + y = 0 ∧ x ≠ 0`; `typeB_zero_is_equatorial` (decide) | proved; Batch4_1's reservoir instances at charge ±1, Δ = 1 are false as written | cancellation inside [1]; unrelated to the threshold |
| partition vs power | `sumR 10 [3,3,3,3,3] ≥ 10 ∧ R 10 3 = 3 ∧ R 10 9 = 9 ∧ R 10 27 = 0`; `isPartition` | 9/10 proved on literals; `messina_ono_concrete` **negated** by Aristotle (list sums to 41, not 42), still sorry in `Theorem120_Fix` | additive pools cross gradually, powers jump |
| reclassification by scale | `reclassification_by_scale (h₁ : \|x\| ≥ Δ₁) (h₂ : \|x\| < Δ₂) : N Δ₁ x = x ∧ R Δ₂ x = x`; `IsInShell` | proved (output97) | **the only proved [1] → [0.0e] mechanism: change Δ, not x** |
| half-threshold absorption | `half_threshold_absorbs_spike (μ < Δ/2) (ε < Δ/2 − μ) : μ + ε < Δ`; `zone_returns_to_reservoir_after_spike` | proved (output98, linarith) | the closest injection-safety statement: an increment ε keeps μ in [0.0e] iff μ + ε < Δ |
| stateful reservoir | `cycleStep Δ s input := let total := s.remainder + input; ⟨s.observable + nullify Δ total, remainder Δ total⟩`; `evaporation_step` (reservoir − chunk) | **definition only**, no theorem | already the inject-then-nullify cycle; the only place a reservoir is decremented |
| norm vs componentwise | `nullifyComponentwise`, `nullifyNorm` (threshold on \|v\|²), `nullifyBloch` | conservation proved; the difference is `#eval` only; `Nullification_Bloch.lean` has zero theorems | the "nullify \|r\|" vs "nullify z" fork the data decided |
| NLoS duality | `NLoSContext` with a two-sided inverse H; `EvanescentSpace = R-range∖{0}`, `PropagatingSpace = N-range∖{0}` | proved (41 theorems, 0 sorry) | H is a linear iso unconnected to N; the two "spaces" are complementary sets, not subspaces |
| information predicates | `hasInformation x := x > 0`, `LosesInformation f := ∃ x > 0, f x = 0` | defined, never used; under them N *loses* information for every Δ > 1 | opposite of the file's prose |
| entropy H_N | — | **absent**; the only entropy→class map is a lookup table on hardware numbers (`entropy_to_class`, reversed ordering) in the thread flagged provisional | |
| solver code | `nullification_mps.py`: N on the Schmidt spectrum with a relative Δ = 1e-10·S[0]; R accumulated, never reused. `nullification_holographic.py`: three-class truncation (keep all [1], half of [0.0e], none of [0]) + `exp(−0.01·R)` shrinkage | executable, no derivation | the only running three-class algorithm |

**Injection.** The word occurs only as "degeneracy injection" of CNOTs (`EmpiricalBridge.lean:130`), as AXLE's import injection, and as
Mathlib injectivity. No definition, theorem or class. (a)

### 1.4 Proof-status census (key files; counted by hand where grep is unreliable)

| file | theorems | proof-position sorry | note |
|---|---|---|---|
| Nullification_Core | 8 | 0 | the reference core |
| Batch1/2/3 (target / `_aristotle`) | 10 each | 10 / 0 | `_v2` copies are mojibake (UTF-8-as-cp1252) and do not parse |
| Batch4_2 (degenerate zeros) | 16 | 0 (the one `sorry` token is prose) | one headline instance false as written |
| Batch12 partition-vs-power (target / aristotle) | 10 / 11 | 10 / 1 | `messina_ono_concrete` negated |
| Batch13 TCO₃ (original / Aristotle) | 10 / 10 | 8 / 0 | two theorems negated, fixed with extra hypotheses |
| Batch14 enforcement (both) | 12 / 11 | 0 | `_MasterEnforcement` copy is mojibake |
| Batch17 toroid / batch17 | 26 / 23 | 3 / 0 | Aristotle omitted the 3 |
| MNFmeetsDavisSet4, wormhole_4, merged | 19 / 13 / 71 | 0 | ejection predicate + probes |
| output56 / 57 / 89 | 35 / 19 / 41 | 0 | signed; multiplicity; NLoS |
| output86 pole probe | 19 | 1 + 1 axiom | header says "Zero sorry" |
| full_cascade_loop_breaker | 15 | 4 locations / 6 terms | header says "two" |
| Quantum_Nullification_Aristotle | 32 | 25 | never closed |
| Nullification_Aristotle_Extension (+ copy) | 37 | 26 / 26 | general `list_conservation` among them |
| Nullification_Bloch / Phase3 / Phase4 / Robinson | 0 | — | `#eval` only |

Corpus-wide: 352 raw `sorry` lines in 73 of 301 files (≈243 in proof position); `axiom` declarations in 29 files of three kinds —
proved results re-axiomatised (`aristotle_stress_test_synthesis`), hardware/arithmetic facts as axioms (`ibm_mass_gap_positive : 192/100 > 0`,
BlueQubit job ids), and genuine unproved assumptions (`func_eq_deriv`, `montgomery_pair_correlation`, `st_is_RingFlux_on_finite`);
~1500 `native_decide` on literals; eight mojibake files; `Batch4_1/4_2` and `wormhole_3` v1 contain `decide`/`simp` proofs of false or
ill-typed statements and would not compile as on disk. Twenty numbered inter-file inconsistencies are listed in `catalogue.md` §4 (one-sided
vs two-sided operators; Δ/2 probe centre vs Δ ejection edge both called the ejection locus; `tau_half` naming collision; missing imports).

### 1.5 Corrections-log flags honoured

The compilation's own log marks: (1) the isolation-vs-suppression inversion as fixed; (2) the Q7 provenance as unconfirmed, so the photon-
isolation results V6–V13 are **provisional**; (3) the Grover amplification as **disproven/pending** (no executed result); (4) the
6√2·Λ_QCD mass-gap law as **abandoned**; (5) the Lean status of the RH chain as **conditional, not complete**; (6) QCD↔QED not interchangeable.
None of those threads contributes an operation to the algebra below; the only entropy→class object in the corpus belongs to thread (2).

---

## 2. The extension (proposed)

Notation: Δ > 0, x ∈ ℝ, s = sgn x, u = |x|; G_Δ := {0} ∪ {|x| ≥ Δ} = range N (corpus `spectral_gap`); the reservoir is (−Δ,0) ∪ (0,Δ).
Tags: **[C]** corpus, **[P]** proposed, proved in prose and numpy-tested unless marked otherwise, **[D]** data.

### 2.0 The design decision: values and representations

**Lemma (no value-level injection).** [P] If f : ℝ → ℝ conserves content in the only sense available at the value level, f(x) = x, then f = id and
N(Δ, f x) = N(Δ, x). So an observable value cannot be "pushed below Δ" while keeping its content. The additive map x ↦ x + a with sgn a = −sgn x
does move it, but changes the content; that is negative accumulation and needs no new theory (the catalogue's `inject Δ x y := remainder Δ (x+y)`,
`eject Δ x y := nullify Δ (x+y)` are exactly this, and every theorem about them is a renaming of `conservation`, `remainder_stores_intact`,
`nullify_routes_intact`, `not_linear`; the corpus's `half_threshold_absorbs_spike` is their one safety margin).

The content-conserving injection therefore acts one level up, on **representations**, which the corpus already carries implicitly (Batch3/Batch12
list sums `sumN`, `sumR`; output89's Hadamard pool; the Pauli-path and Schmidt expansions of the OTOC map):

**Def (representation, reading, hidden part).** [P] A representation of x is a finite tuple ρ = (p_1,…,p_k) with content(ρ) := Σp_i = x;
(x) is the exact representation; ρ is *same-sign* if all nonzero pieces share a sign. The **piecewise reading** ν_Δ(ρ) := Σ_i N(Δ,p_i)
("nullify, then pool"); the **hidden part** h_Δ(ρ) := Σ_i R(Δ,p_i); "pool, then nullify" is N(Δ, content ρ).

**Prop (representation conservation).** [P] ν_Δ(ρ) + h_Δ(ρ) = content(ρ) for every finite ρ (termwise conservation + finite additivity).
This is the general list theorem the corpus states only for three instances. Non-distributivity is the statement ν_Δ ≠ N_Δ∘content
(corpus witness ρ = (Δ/2, Δ/2): ν = 0, N(content) = Δ). **Everything below is the study of the defect ν_Δ − N_Δ∘content.**

**Where the simulators sit.** [D] A BlueQubit pauli-path run at threshold δ returns ν_δ of the Pauli expansion that the platform's
transpilation variant produced (`max_paulis` = pieces kept at the expansion's peak); an MPS run at bond dimension χ returns a value computed
from the χ largest Schmidt pieces at every cut. Both are piecewise readings; neither is a value-level N of the answer.

### 2.1 Ejection as an operator

**Def.** [P] E(Δ,x) := sgn(x)·max(|x|, Δ) for x ≠ 0, E(Δ,0) := 0. Equivalently: identity on G_Δ, Δ·sgn(x) on the reservoir.

**Properties.** [P, tested T2/T3]
* range(E) = G_Δ and E∘E = E; N∘E = E, E∘N = N; R∘E = 0; E∘R = Δ·sgn(R x).
* **gap jump:** E − N = Δ·sgn(x)·1_{0<|x|<Δ}; classify(E x) ∈ {[0],[1]}: E empties the reservoir upward exactly as N empties it downward
  (Batch14's "the reservoir class is unstable" read as its two resolutions).
* dilation covariance E(λΔ, λx) = λE(Δ,x); threshold semilattice N_a∘N_b = N_max(a,b), E_a∘E_b = E_max(a,b), N_a∘E_b = E_b if b ≥ a else N_a;
  for b < a, E_a∘N_b is a genuinely two-threshold map (collapse below b, eject [b,a) to a, keep ≥ a).
* **floor/ceiling adjunction** on P = [0,∞): for gapped g ≥ 0, `g ≤ x ⇔ g ≤ N(Δ,x)` and `x ≤ g ⇔ E(Δ,x) ≤ g`. So E ⊣ incl ⊣ N: N is a kernel
  (interior) operator, E a closure operator, N ≤ id ≤ E, both monotone (negative x: same with the order reversed). This is the precise sense of
  "adjoint". There is **no linear adjoint**: N is not linear (`not_linear` [C]); the paper's "N = N*" refers only to the linear ∏P_j form.
* The corpus predicate becomes an identity: `IsEjectionThreshold Δ (E(Δ,x))` for every positive-reservoir x, and `ejection_probe_reading` [C]
  reads NorthProbe(E x) = Δ/2.

*Proof sketch.* On G_Δ both E and N are the identity; on the reservoir N x = 0 and E x = Δ·sgn x; every identity is a case split on |x| against
the thresholds. For the adjunction: g ≤ x < Δ with g gapped forces g = 0 = N x; 0 < x < Δ and x ≤ g gapped forces g ≥ Δ = E x. ∎

**Three routes to ejection.** [P] For reservoir x: dilation x ↦ λx lands exactly on Δ at λ* = Δ/|x|; accumulation (n copies) lands in
[Δ, Δ+|x|) at n* = ⌈Δ/|x|⌉ (the corpus `accumulation_crosses_threshold` is n* = n for x = Δ/n); a multiplicative orbit {λᵐx} overshoots by
< factor λ. That is Batch12's partition-vs-power written as two flows toward the same E. Along the dilation flow the probe x(t) − Δ/2
rises monotonically from −Δ/2, crosses 0 at the midpoint, and reads Δ/2 exactly at ejection — the corpus statement as an endpoint
(Batch17's *critical cascade* is any discretisation of this flow stopped before t*).

**Worked example (exact arithmetic).** Δ = 1, y = 0.4 ∈ [+0.0e]: E(y) = 1.0, J(y) = 0.6, λ* = 2.5, n* = 3 (0.8 < 1 ≤ 1.2), NorthProbe(E y) = 0.5 = Δ/2.
Composition: N_{0.5}∘E_{1.0}(0.3) = 1.0 (= E_{1.0}); N_{1.0}∘E_{0.5}(0.3) = 0 (= N_{1.0}).

**Worked example (real data).** [D] For a scalar, the reading at ejection is Δ itself (|v|/Δ = 1, probe Δ/2). For a real cascade it is not:
S3 q17 (truth −0.8117) on the BlueQubit platform's own pauli-path ladder reads 0 at δ = 10⁻², **−0.3264 at 10⁻³**, −0.8102 at 10⁻⁴: the
reading at the ejection rung is 0.40 of the final value with the final sign, and |v(δ*)|/δ* ≈ 330. (On the lab's local 21-rung ladder, from
which the statistics that follow come, the same ID ejects about 50× coarser, δ* = 0.0512, with v(δ*) = −0.198 = 0.24 of truth; the two
ladders are different truncation schemes and are not interchangeable.) Over the 28 S3 IDs with a local 21-rung ladder: |v(δ*)|/|truth| median 0.387 (IQR 0.27–0.59),
0.853 two rungs finer, sign correct 25/28; on the platform without truth: G3 median 0.36 (n 10, smaller than the fine draw in 10/10,
sign 8/10), G4 0.36 (n 5, sign 5/5). The value that appears at ejection is pooled from pieces each far below Δ (§2.4). So E is the right
operator for *one value*; what a cascade ejects is a pool, and the only probe-like reading settled at ejection is the sign.

### 2.2 The deficit J (the operator that generates the algebra)

**Def.** [P] J(Δ,x) := E(Δ,x) − x = (Δ − |x|)·sgn(x) on the reservoir, 0 on G_Δ.

**Prop.** [P, tested T2] On the reservoir J replaces |x| by Δ − |x|: it is the **reflection of the reservoir about its midpoint Δ/2** (fixes ±Δ/2).
Hence (a) J∘J = R and J∘J∘J = J (tripotent); (b) E = id + J and N = id − J∘J (pointwise); (c) N∘J = J∘N = J∘E = 0, E∘J = E∘R; (d) **probe
swap:** for 0 < x < Δ, NorthProbe(Δ, J x) = SouthProbe(Δ, x) — the corpus probe pair (`probe_balance`, N + S = 0 [C]) is the pair of readings
before and after the deficit; the ejection point x = Δ is the J-image of x → 0⁺ and the midpoint (probe 0) is the unique J-fixed reservoir value.
*Proof.* |J x| = Δ − |x| ∈ (0,Δ) with the sign of x, so J(J x) = x on the reservoir and 0 elsewhere, which is R; the rest is substitution. ∎
Consequently {N, R, E, J} is the closure of the single map J under composition and pointwise ±id.

**Worked example.** Δ = 1: J(0.3) = 0.7, J(J(0.3)) = 0.3 = R(0.3); NorthProbe(J(0.3)) = +0.2 = SouthProbe(0.3); J(2.5) = 0 (no deficit on [1]).

**Remark (metric projection; placement §9 + this synthesis).** [P] The Euclidean projection P onto the non-convex set G_Δ sends a reservoir value
to 0 if |x| < Δ/2 and to Δ·sgn x if |x| > Δ/2 (set-valued at Δ/2). So the corpus probe x − Δ/2 is exactly P's **decision function**, N its lower
branch and E its upper branch, and "the probe reads Δ/2 at ejection" is the branch switch. One further line (checked numerically in
`check_synth.py`): on the reservoir, away from the midpoint, **P + P∘J = N + E** — the deficit swaps the branch P takes. This gives the
probes a standard meaning with no toroid or wormhole content; it is a calculation, not a corpus theorem, and it was not tested as an estimator.

### 2.3 Injection as an operator

**Def.** [P] Fragmentation injection I_k(x) := (x/k, …, x/k) ∈ ℝ^k, k ≥ 1; weighted injection I_w(x) := x·w with Σw = 1 (negative weights give a
mixed-sign representation); refinement refine_k(ρ) splits every piece into k equal same-sign pieces. **Compaction** C(ρ) := (content ρ).
**Injection index** k*(Δ,x) := ⌊|x|/Δ⌋ + 1, the smallest k with every equal piece sub-threshold.

**Theorem (fragmentation injects, compaction ejects).** [P, tested T4]
(i) **ν_Δ ∘ I_k = N_{kΔ}** and ε_Δ ∘ I_k = E_{kΔ} (ε_Δ(ρ) := Σ E(Δ,p_i)): fragmenting into k equal pieces and reading piecewise is nullification at
the k-fold dilated threshold — **injection is threshold dilation**. With dilation covariance, N(kΔ, x) = k·N(Δ, x/k): I_k acts on the reading
exactly as x ↦ x/k acts on the value.
(ii) content(I_k x) = x; C∘I_k = id; I_k∘C is idempotent (a retraction onto k-equal representations); I_j∘I_k = I_{jk}: the injections form the
multiplicative monoid ℕ≥1 — I_k is neither idempotent nor nilpotent, only **eventually nullifying**: ∀x ∀Δ ∃K ∀k ≥ K, ν_Δ(I_k x) = 0, the dual
of the corpus accumulation theorem.
(iii) ν_Δ(I_k x) = 0 ⇔ |x| < kΔ ⇔ k ≥ k*. So for every observable x there is a k making every piece [0.0e] while the pool is [1]: a Type A
degenerate zero on demand.
(iv) **N and E see through injection, ν does not:** N(Δ, content(I_k x)) = N(Δ,x), E likewise, ν_Δ(I_k x) → 0. The non-distributivity theorem is
the statement ν_Δ∘I_k ≠ N_Δ∘content∘I_k.
(v) For reservoir x, the n*-fold copy (x,…,x) has ν_Δ = 0 and N(Δ, C(ρ)) = n*x ≠ 0: compaction ejects what fragmentation injected.
*Proof of (i).* ν_Δ(I_k x) = k·N(Δ, x/k) = k·(x/k)·[|x|/k ≥ Δ] = x·[|x| ≥ kΔ] = N(kΔ, x); the same for E. ∎

**Answer to "inverse, adjoint or neither".** E and N: not inverse (both idempotent, non-injective), order-adjoint (§2.1), no linear adjoint.
I_k and C: one-sided inverse (C∘I_k = id). I_k and E: neither — different levels; the composites are (iv)–(v).

**Worked example (exact).** Δ = 1, x = 2.5 ∈ [1]: k* = 3, I_3 x = (0.8333, 0.8333, 0.8333), ν_1 = 0, content 2.5, δ*(I_3 x) = 0.8333;
ν_1(I_k 2.5) for k = 1..4 = (2.5, 2.5, 0, 0) = N_k(2.5); ε_1(I_3 2.5) = 3.0 = E_3(2.5).

**Worked example (real data).** [D] G3 q34, one threshold 10⁻⁵, two transpilation variants of the same circuit: `max_paulis` 215,848,196 → ν = +0.15995;
`max_paulis` 388,936,944 → ν = 0.0000 (fragmented all the way to an exact-zero reading; the compact value is the one used in G3_v11). S3 q17:
the exact representation would eject at δ* = |x| = 0.81; the platform's Pauli-path representation ejects in [10⁻³, 10⁻²) (the local
propagator's at 0.0512): the one observable value is
carried by pieces each a hundred times smaller — (iii) on the platform's own expansion. On S3 with truth, a 3.8× larger expansion of the
same unitaries (random topological re-orderings) lowers δ* by half a √2-rung in 17/28 and 20/28 IDs, and at the rungs where two
representations disagree on the class the zero comes from the larger expansion 26/32, 22/28, 30/37 (p ≤ 5e-4); the compact representation
is closer to truth in 325/429 and 324/420 rung-readings (p ≤ 1e-27).

### 2.4 The cascade: readings over a threshold ladder

**Def.** [P] A ladder is Δ_1 > Δ_2 > … > Δ_m > 0 (coarse to fine); the cascade of ρ is (ν_{Δ_1}(ρ), …, ν_{Δ_m}(ρ)). By the semilattice law this is
*not* N_{Δ_m}∘…∘N_{Δ_1} (which is N_{Δ_1}): a ladder is m independent nullifications of one representation. (Data: identical (threshold, variant)
⇒ bit-identical reading, 16/16 inventory pairs; 28/28 G3 and 53/53 G4 repeats in the lab.)
**Ejection threshold of a representation** δ*(ρ) := sup{Δ > 0 : ν_Δ(ρ) ≠ 0} (sup ∅ = 0); ν is piecewise constant in Δ with breaks at the |p_i|, so δ*
is the largest magnitude at which the reading is nonzero.

**Theorem.** [P, tested T4/T5] (a) δ*((x)) = |x|. (b) δ*(ρ) ≤ max|p_i| ≤ Σ|p_i|. (c) same-sign ρ: δ*(ρ) = max|p_i| ≤ |content|, equality iff exact.
(d) same-sign ρ: |ν_Δ| is non-increasing in Δ, |ν_Δ| ≤ |content|, sgn ν_Δ = sgn content when nonzero, ν_Δ = content once Δ ≤ min|p_i|.
(e) **refinement theorem:** a same-sign refinement never increases |ν_Δ| and never raises δ* (a surviving piece splits into pieces of which at
most all survive; a dead piece has only dead sub-pieces). (f) mixed-sign ρ: none of (c)–(e) need hold — ν need not be monotone ((3,−3,1):
ν_3 = ν_2 = 0, ν_1 = 1), |ν| can exceed |content| ((3,−2.9) at Δ = 3: ν = 3 > 0.1), δ* can be below max|p_i| ((2,−2,0.5): δ* = 0.5), refinement
can increase |ν|.
**Corollary (what `max_paulis` measures).** Among same-sign representations of one content, more (hence smaller) pieces read smaller at fixed Δ
and eject later. The piece count of a Pauli expansion is a proxy for its refinement; G3's "fewer `max_paulis` ⇒ larger value" is (e) on data and
the sign flips are (f): real Pauli pieces are mixed-sign.
**Theorem (an exact-zero reading is uninformative).** [P] ν_Δ(ρ) = 0 is consistent with content 0 ([0]) and content ≠ 0 ([0.0e]) — (0) and
(0.4, 0.3) at Δ = 1 — and a zero at one rung does not imply zero at a finer rung (ν_{0.35}(0.4, 0.3) = 0.4). A zero reading is an abstention,
never evidence for [0], and must not be averaged with nonzero readings of the same content.

**Worked example (real data).** [D] S3 q17 platform ladder (BlueQubit pauli-path, not the local one): 0 (10⁻²), −0.3264 (10⁻³), −0.8102 (10⁻⁴), −0.8088 (10⁻⁵); truth −0.8117 — monotone climb from the
first survivors to the content, as (d); the tiny 10⁻⁴ → 10⁻⁵ wobble is (f). S3 q8: 0 at 10⁻⁴, +0.2608 at 10⁻⁵ (truth +0.2610): a zero that was
[0.0e]. Over the 28 S3 IDs with complete local ladders: Spearman(log δ*, log |truth|) = +0.60 (p 7e-4), log-log slope 0.65 (a scalar would give
slope 1 through δ* = |truth|), accumulation factor |truth|/δ* median 11.6 (IQR 3.7–16.8); Spearman(log expansion size, log δ*) = −0.83
(platform: −0.54 on G3 n 27, −0.52 on G4 n 21). The bottleneck b = min_t max_P|c_P(t)| of the fine cascade ranks δ* (Spearman +0.875) but
δ* ≈ b/7 (log₂ median −2.81; 0/28 within two rungs). **The ejection threshold of a cascade is emergent**, not a scalar crossing.

**Limit of the representation model (the lab's central finding).** [D] The model above reads a *final* partition. The real cascade truncates
*in process*: every coefficient is thresholded at every step. On 25/25 S3 IDs with a pooled-zero rung, the in-process cascade reads exactly 0
at a Δ where post-hoc nullification of the exact final pieces still keeps 1–14 pieces whose sum is nonzero with the truth's sign
(|post-hoc|/|truth| median 0.68); the cascade dies a median 1.58 octaves *below* the largest exact piece (q9: pooled 0 at 2.56e-2 while the
reservoir holds 87 % of the truth). So N∘(dynamics) ≠ (dynamics)∘N on every ID tested: on this data, nullification inside the dynamics was more
confining than nullification of the final partition — an empirical regularity of these cascades, not a general theorem (for
L v = (v₀ + v₁, 2v₁) and v = (2Δ, −Δ/3) the in-process reading on coordinate 0 exceeds the post-hoc one, 5Δ/3 > Δ). In the algebra this is `not_linear` realised repeatedly along the path; a time-indexed
version of ν is the missing object (§6). A two-coordinate witness for the Lean sketch: v = (Δ, 0), L v = (v₀/2 + 2v₁, v₀/2): L²v = (5Δ/4, Δ/4),
post-hoc N gives (5Δ/4, 0), in-process gives (0, 0) because the first step split Δ into (Δ/2, Δ/2) and both halves were killed before they
could re-merge (checked in `check_synth.py`).

### 2.5 Fragmentation ⇄ compaction

**Statement.** [P] Fragmentation (refinement, I_k) and compaction (C) are the two directions of one move on representations; N and E are
invariant under it (they act on content), ν is not. For same-sign pieces compaction can only raise |ν_Δ| and δ* (refinement theorem); for
mixed-sign pieces it can lower |ν| (the residue regime, §2.6). The operational rule that follows — among readings of one content at one Δ
prefer the most compact representation, never average readings across representations, treat an exact zero as an abstention — is
**rule A**.

**Counterexample to a naive version.** [P] "The reading with fewer pieces is always closer to the content" is false for mixed signs: (3, −2.9)
reads +3 at Δ = 3 while its compaction (0.1) reads 0 — the compact reading is right and the fragmented one is a pure residue, but
(−3, 2.9, 0.2) reads −3 for the same content: more pieces, wrong sign. Rule A's direction was settled empirically, not by the theorem.

**Worked example (real data).** [D] G3: v5 (compact-threshold selection) 373; v7 (per-ID mean of repeated draws including exact zeros and
fragmented ones) 326, i.e. −47; v10 (rule A with v5's coarse-threshold down-weights) 379; v11 (+ one more compact 10⁻⁵ hit on q34, +0.16) **430/800**.
9/9 same-threshold G3 pairs: the draw with 2.0–5.3× fewer `max_paulis` has the larger |v| (sign test p ≈ 0.002); 2/9 flip sign (q0, q8).
The lab's wider count: the zero draw is the larger expansion in **13/13** distinct same-threshold variant pairs over 11 IDs (one-sided
p 1.2e-4; the lab's raw tally of 23/23 counted repeated draws of identical variants, which are the same nullification and not independent
events — inventory C1); G4 2/4 (no contrast: its
variants differ by < 5 % in `max_paulis`). On S3 with truth the local propagator ranked "fewest `max_paulis`" first among selection rules.

### 2.6 The signed cancellation residue and the sign gate

**Def.** [P] res_Δ(ρ) := ν_Δ(ρ) − N(Δ, content ρ) = R(Δ, content) − h_Δ(ρ): the reservoir content of the value minus what the pieces hide. ρ is a
*pure residue* at Δ if |content| < Δ and ν_Δ(ρ) ≠ 0.

**Theorems.** [P, tested T5/T6]
* Same-sign readings are sign-safe: ν_Δ(ρ) = 0 or sgn ν = sgn content; res = 0 when every nonzero piece survives.
* For every Δ and every reservoir x there are mixed-sign ρ⁺, ρ⁻ of x reading +Δ and −Δ (x = 0.1, Δ = 3: (3, −2.9) → +3; (−3, 1.55, 1.55) → −3);
  both are pure residue; exactly one has the sign of x.
* **Two-piece sign safety.** With ≤ 2 nonzero pieces a nonzero reading has the content's sign. A wrong-sign reading needs ≥ 3 pieces, and if
  its survivors are coherent then the true-sign content is hidden in a pool of ≥ 2 sub-threshold pieces summing beyond Δ — a Type A degenerate
  zero (`IsDegenerateZero_TypeA` [C]) of the true sign. "Fragmentation flips the sign" means the opposite-sign expansion was *injected*, not cancelled.
* **The gate.** Let r_1..r_m be nonzero readings of one value from several representations. (a) If both signs occur, at least one reading is
  residue and no function of the readings can say which (the same pair {+Δ, −Δ} arises from x = +0.1 and from x = −0.1). (b) Any rule that
  outputs a sign on a contradictory multiset is wrong on some value, so **abstention on contradiction is forced**. The "else keep the common
  sign" half is not safe either: a coherent multiset is realisable from a value of the opposite sign (M = {+2, +3}, Δ = 1, x = −1 via
  (2, −0.75×4) and (3, −0.8×5)), so the only reading-only rule that never asserts a wrong sign is the constant 0, and the gate's standing is
  empirical (G4: v7 118 against v8 56 and v9 54) rather than a theorem. (c) **Full realisability:** for every x, Δ and every multiset M of readings with
  |r| ≥ Δ there are representations of x reading exactly M (ρ_r = (r, (x−r)/j, …, (x−r)/j), j = k*(Δ, x−r)). So without a structural assumption
  on how the simulator fragments, readings carry no information at all: the gate is a **minimax** rule, coherence is **not a certificate**, and
  the sign information coherent single readings did carry on G4 is an empirical property of the platform's expansions. (d) A zero reading is
  an abstention, not a vote.
*Corpus link.* (a) is `SignedTriple.is_degenerate` / `mixed_can_cancel` [C] read at the level of readings; the gate's 0 is a Type B zero
("probe zero, content nonzero", `IsDegenerateZero_Unified` [C]), never a [0] claim; `one_sided_sum_zero_iff` [C] is why one-signed pools cannot fake a zero.

**Worked example (real data).** [D] G4 at the API floor δ = 10⁻⁵, where almost every reading is ~10⁻⁴ (sub-resolution). Three IDs read with both
signs across variants: q22 (−7.6e-6 / +1.4e-5), q24 (−1.7e-4 twice / +6.9e-5 three times), q25 (+4.2e-5 three times / −6.9e-5). Gating them to 0
took G4 from **48 (v6) to 118 (v7)**. The stricter gate that also zeroed single-reading IDs scored 56 (v8); majority sign scored 54 (v9): (c) cuts
both ways. The far-corner IDs q36 (−1.1e-2, −1.2e-2 across two variants) and q37 (−2.3e-2, reproduced) are coherent and resolved. The residue
algebra explains *why* zeroing contradicted IDs is the right abstention; it does not predict the magnitude model that took 118 → 298
((N_min/N)^p, p = 2, 3, 4, 6, 9 → 173, 222, 256, 290, 298; p = 13 fell to 286), which is an ordering statement (§2.4 corollary).
On S3 with truth the residue is visible directly: the signed residue |Σp|/Σ|p| of the exact piece decomposition is a function of |truth|
(Spearman +0.92, n 26; median 0.50; |truth| < 0.07 → 0.23, |truth| ≥ 0.3 → 0.955); the five IDs whose largest piece exceeds |truth| (ratio
1.02–2.15: q6, q15, q19, q24, q29) are cancellation residues, and the wrong-sign ejection readings q4 (−0.016 vs +0.110), q6 (+0.101 vs −0.149),
q8 (−0.021 vs +0.261) are residues of the first surviving pieces — the local, truth-checked counterpart of the G4 gate case.

### 2.7 Soft vs hard nullification

**Def (gated operators).** [P] For a witness w ∈ [0,1] (here the Bloch length |r_q| of the same job) and a gate g : [0,1] → [0,1],
S_g(x; w) := x·g(w), R_g := x − S_g. Hard gate g_H(w) = [w ≥ Δ] gives `nullifyBloch` [C] applied to the Z component; soft gate
g_{Δ,p}(w) = min(1, w/Δ)^p gives the OTOC map's pre-registered `soft(D)` (p = 1) and, with Δ = 1, p = ½, the G2_v9 correction z·|r|^½ (after the
half step in log χ).

**Theorem (hard gates are characterised by idempotence and pass-or-kill).** [P, tested T7] With the witness fixed: S_g∘S_g = S_g for all x ⇔
g(w) ∈ {0,1} ⇔ S_g is binary (S_g x ∈ {0, x}: Batch14's "discrete transition"). A soft gate has no spectral gap in x (0 < g < 1 maps Δ′/(2g) to
Δ′/2). Conservation and dilation covariance in (w, Δ) hold for every gate; |N_hard x| ≤ |S_g x| ≤ |x| whenever g ≥ g_H. So the soft family is
a path from N (g = Heaviside in w) to id (g ≡ 1) along which N's two defining properties are switched off and continuity is switched on;
the gap in x is N's own (witness w = |x| with g_H gives S_g = N exactly) and no other witness inherits it.
**Validity condition.** [P/D] S_g is a bias correction only if the witness is biased in a known direction. MPS truncation lowers entanglement, so
on a 1-D chain the reduced state looks purer: |r_χ| ≥ |z_exact| in 12/12 (S2) and 30/30 (G1) qubits, the witness is biased upward, and
multiplying z by g(w) < 1 corrects in the known direction. On the 2-D S3 the bias reverses (|r_χ| < |z_exact| in 20/29 qubits: truncation
breaks refocusing) and the same gate shrinks values already too small. **Prop (z-degenerate zero).** |z| < Δ_z with |r| ≥ Δ_r is a Type B-like
degenerate zero (probe zero, content observable; equatorial vectors the extreme case, `typeB_zero_is_equatorial` [C]): such a z must not be
nullified as [0], but neither may |r| supply its magnitude (inventory E3: S3 q1 has r = (−0.318, 0, 0) and exact z = −0.538).

**Worked example (real data).** [D] G2 (1-D, 36 qubits), χ 128 → 256: q4 z = +0.601, |r| 0.755 → 0.631 (still falling: not converged),
soft = 0.601·√0.631 = +0.477; q6 z = +0.227, |r| 0.403 → 0.231 ([0.0e] at Δ = ½), soft = +0.109. The half-step + sign(z)|z|^1.5 estimator that
won G2 coincides with z·|r|^½ at corr 0.9997; score 549 (v6) → **591/600 (v9)**. The same gate on 2-D S3 loses (inventory F1–F6, within one
bootstrap SE of zero or negative); 2-D MPS at χ ≤ 32 is floating-point chaotic (a 1e-14 angle change moves values by O(1)), so no Bloch
transform can work there. Non-idempotence made concrete: z = 0.8, w = 0.5, p = 1: S = 0.40, S(S) = 0.20.

### 2.8 Composition table (value level) and mixed-level identities

Closed forms of outer_a ∘ inner_b (s = sgn x, u = |x|, m = max(a,b), l = min(a,b), [·] indicator); all sixteen tested at random and at the
boundary values u ∈ {0, a, b, (a+b)/2, |a−b|} (self-test T3b; the 2026-11-01 draft's R_a∘E_b entry was wrong and the test caught it).

| outer \ inner | N_b | R_b | E_b | J_b |
|---|---|---|---|---|
| **N_a** | N_m | x·[a ≤ u < b] | E_b if b ≥ a, else N_a | (b−u)·s·[0 < u ≤ b−a] |
| **R_a** | x·[b ≤ u < a] | R_l | 0 if b ≥ a, else b·s·[0 < u < b] + x·[b ≤ u < a] | (b−u)·s·[max(0,b−a) < u < b] |
| **E_a** | N_b if b ≥ a, else a·s·[b ≤ u < a] + x·[u ≥ a] | a·s·[0 < u < l] + x·[a ≤ u < b] | E_m | (b−u)·s·[0 < u ≤ b−a] + a·s·[max(0,b−a) < u < b] |
| **J_a** | (a−u)·s·[b ≤ u < a] | (a−u)·s·[0 < u < l] | 0 if b ≥ a, else (a−b)·s·[0 < u < b] + (a−u)·s·[b ≤ u < a] | (a−b+u)·s·[max(0,b−a) < u < b] |

Mixed level: C∘I_k = id; I_k∘C idempotent; I_j∘I_k = I_{jk}; N_Δ∘C∘I_k = N_Δ; E_Δ∘C∘I_k = E_Δ; **ν_Δ∘I_k = N_{kΔ}**; **ε_Δ∘I_k = E_{kΔ}**;
|ν_Δ∘refine_k| ≤ |ν_Δ| (same sign); ν_Δ + h_Δ = content; res_Δ = ν_Δ − N_Δ∘content; ν_Δ(I_w x) = x·Σ_{|w_i| ≥ Δ/|x|} w_i.

### 2.9 What this synthesis adds beyond the four reports

Small and stated as such: (i) the reconciliation of the two injection proposals — the catalogue's additive `inject Δ x y` (changes content; nothing
new) and the algebra's fragmentation I_k (conserves content; new) — as the value- and representation-level faces of one object; (ii) the
placement of the lab's in-process result as the **boundary of the representation model** (§2.4): ν reads a final partition, the real cascade
thresholds in time, and the two differ on 25/25 IDs, which fixes what the next formal object must be; (iii) the one-line branch-swap identity
P + P∘J = N + E on the reservoir (§2.2), which ties the metric-projection reading of the probes to the deficit; (iv) the Lean sketch (§5) that
puts the proposals of all three theory reports into one file with the lab's witness. Nothing here was machine-checked.

---

## 3. What the OTOC data demonstrated, operation by operation

| operation | demonstration | numbers (with n) | where |
|---|---|---|---|
| N as the platform's cut; idempotence | same (δ, `max_paulis`) ⇒ bit-identical value | 16/16 (inventory C1); 28/28 G3, 53/53 G4 (lab) | inventory, lab §1 |
| exact zero = [0.0e], never [0] | zero draws with ≥ 2.4 M strings kept were non-detects; averaging them lost | S3 q8 0 at 10⁻⁴ / +0.2608 at 10⁻⁵ (truth +0.2610); 4/30 S3 IDs zero at 10⁻⁴ with nonzero truth; G3_v7 326 vs v5 373 (−47); S3 finest-nonzero rule r² 0.9975 vs zeros-kept 0.9847 | STATUS, inventory A3, lab |
| **injection by fragmentation** (ν∘I_k → 0; refinement theorem) | larger expansion of the same unitary reads 0 or smaller | G3 9/9 pairs (p ≈ 0.002); 13/13 distinct zero-from-larger variant pairs (p 1.2e-4; 23 draws with repeats); δ* vs `max_paulis` Spearman −0.54 (n 27) / −0.52 (n 21); S3 local −0.83 (n 28); variants 26/32, 22/28, 30/37; δ* −0.5 rung for 3.8× expansion in 17/28, 20/28 | inventory D2; lab §1–2 |
| **compaction / rule A** | select the compact representation, never average | G3 373 → 379 → **430**; v7 326; compact closer to truth 325/429, 324/420 (p ≤ 1e-27) on S3 | STATUS, lab §2 |
| residue (mixed sign; (f)) | overshoot and sign flips from dropped opposite-sign pieces | S3 3/30 overshoot (q15 1.12, q19 1.37, q27 1.02); 2/9 G3 flips; S3 wrong-sign ejection readings q4, q6, q8 | algebra §5.6, lab §2 |
| **sign gate** | contradicted signs → 0 | G4 **48 → 118** (q22, q24, q25); v8 56, v9 54; q36/q37 coherent | ALL_NOTES G4_v6–v9 |
| sign survives, magnitude does not | sign settled at ejection | S3 25/28 at δ*_first, 27/28 at δ*_stable; G3 8/10; G4 5/5; 5 of 6 S3 sign errors in the ejection band | lab §2, §5 |
| cancellation residue vs \|truth\| | residue is a function of the value's size | \|Σp\|/Σ\|p\| Spearman +0.92 with \|truth\| (n 26); 5 IDs with max\|p\| > \|truth\| | lab §3 |
| Type A degenerate zero on real pieces | every exact piece sub-threshold, pool observable | 21/26 S3 IDs; window 1.62 octaves; factor 3.07 (medians over the 21 window IDs) (q9: 48 pieces ≤ 0.027 sum +0.444) | lab §3 |
| **ejection threshold is emergent** (not E on a scalar) | δ* tracks \|truth\| with slope < 1 and sits far below it | Spearman +0.60, slope 0.65, factor 11.6 (n 28); bottleneck rank +0.875 but δ* ≈ b/7; platform δ* vs \|v\| null (+0.11, +0.09) | lab §1–2 |
| reading at ejection ≠ Δ/2 | the ejected reading is a pool | \|v(δ*)\|/\|truth\| 0.387 (n 28), 0.853 at δ*/2; platform 0.36 (n 10), 0.36 (n 5); \|v(δ*)\|/δ* 3.2 local, 354 / 8.3 platform | lab §2, §5 |
| **in-process ≠ final-partition nullification** | cascade zero while post-hoc N of exact pieces is nonzero with the right sign | 25/25 IDs (empirical; not a general theorem); log₂(max\|p\|/δ*) +1.58; post-hoc/truth 0.68 | lab §3 |
| per-piece dilation (another "injection") | restores non-zeroness, not accuracy | zeros 15 → 6 of 54 pairs; closer to truth 29/54 (null) | lab §3 |
| dilation covariance on the platform ladder | null (censored ladder) | Spearman +0.11 (n 27), +0.09 (n 24) | lab §1 |
| **soft gate z·\|r\|^½** | 1-D bias correction | G2 549 → **591** (corr 0.9997 with the submitted estimator); S2/G1 \|r_χ\| ≥ \|z\| 12/12, 30/30 | STATUS, inventory F6 |
| soft gate in 2-D | fails | S3 \|r_χ\| < \|z\| 20/29; inventory F1–F6 within ±0.03; hard variants killed | inventory, lab §4 |
| Bloch length as a probe | contracting witness in 1-D only | S2 contraction 0.20, sign persistence 11/12, Spearman(last \|r\| step, error) +0.92 (n 12); S3 persistence 5/20, ρ −0.06 (n 29); G2 persistence 97/115 but contraction 0.96 | lab §4 |
| magnitude cue (ordering, not residue) | sharper ordering by expansion size | G4 118 → 173 → 222 → 256 → 290 → **298** (p = 2…9); 286 at p = 13 | STATUS |
| probes / leveling / toroid / wormhole / NLoS | no data counterpart | — | catalogue §2 |

Total hackathon score 1919 (S1–S3 300, G1 300, G2 591, G3 430, G4 298). Every MNF effect in that score is explained by N, R as a store, Σ
(non-distributivity), the signed coherence test and the 1-D witness bias; nothing from the probe/toroid/wormhole layer was needed.

---

## 4. Literature placement

| MNF item | standard name | closest reference | what MNF adds |
|---|---|---|---|
| N(Δ,x) keep-or-kill | hard thresholding; dead-zone quantiser; prox of the ℓ0 penalty; retraction onto a semi-continuous set | Donoho & Johnstone 1994; Blumensath & Davies 2008; Sun, Zheng & Li 2013 | the class vocabulary applied across χ, δ and Bloch length |
| R = x − N, N + R = id | residual; discarded weight of a truncation | White 1992; Schollwöck 2011 | insists R is tracked and can re-enter |
| [0] / [0.0e] / [1] | not detected / detected-not-quantified / quantified; left-censoring; IEEE-754 subnormals | Currie 1968; Tobin 1958 (the "Tobit" model); Helsel 2006; IEEE 754 | the exact-zero-is-a-non-detect rule in circuit simulation |
| non-distributivity, pool accumulation | nonlinearity of thresholding; truncate-before- vs after-merge; block thresholding; integrate-and-fire | Rudolph et al. (arXiv:2505.21606, 2025; PRX Quantum 7, 032001, 2026); Cai 1999; Lapicque 1907 / Abbott 1999 | "fragmentation": a less compact representation of the same content reads less |
| degenerate zero Type A / Type B | dangerously irrelevant variable (A); destructive interference / sign problem (B) | Fisher 1983; Troyer & Wiese 2005 | the A/B pairing; "a contradicted sign is a residue" |
| signed classes, one-sided pools | sign-preserving shrinkage; sign consistency; 1-bit compressive sensing (direction only) | Zhao & Yu 2006; Jacques et al. 2013 | magnitudes still matter (v9 54 < v7 118) |
| "[0.0e] is empty" as a hypothesis | beta-min condition; semi-continuous domain | Bühlmann & van de Geer 2011 Cor. 6.8; Sun, Zheng & Li 2013 | the sign gate as the fallback when it fails |
| partition vs power | products of path coefficients vs sums over paths; frequency truncation | Rudolph et al. 2023 (LOWESA) | the expansion-size cue as a magnitude model |
| MPS χ-cut = N | SVD truncation; extrapolation in χ / truncation error | Vidal 2003; Hubig et al. 2018 | Bloch-length convergence meter (1-D only) |
| Pauli-path δ-cut = N | coefficient truncation in sparse Pauli dynamics / Pauli propagation; two convergence classes | Begušić & Chan 2023, 2025; Begušić, Gray & Chan 2024; Gharibyan et al. 2025 | compact-variant selection across transpilations (not found published); residue regime = the non-converging class |
| soft gate z·\|r\|^p | nonlinear sign-preserving shrinkage (firm / garrote / SCAD family) | Gao & Bruce 1997; Breiman 1995; Fan & Li 2001 | the witness-bias validity condition |
| ejection predicate x = Δ; operator E | threshold crossing / first passage; spike; closure operator / ceiling into G_Δ; Galois connection E ⊣ i ⊣ N | Kramers 1940; Redner 2001; Ore 1944; Davey & Priestley 2002 | τ/2 = π, toroid, wormhole: not assessable from the Lean |
| probes x − Δ/2 | decision function of the metric projection onto G_Δ (this exploration) | — | gives the probes a standard meaning without toroid content |
| injection (undefined in corpus) | current injection (integrate-and-fire); re-partition of a coefficient (block thresholding; merge order); magic-state / leakage injection | Lapicque 1907; Cai 1999; Rudolph et al. 2025; Bravyi & Kitaev 2005; Aliferis & Terhal 2007 | fragmentation as injection; ν∘I_k = N_{kΔ}; measured on transpilation variants (9/9, 23/23) |
| 2-D MPS chaos | discontinuity of hard cuts at near-degenerate Schmidt values | McCulloch 2007; Gao & Bruce 1997 | the 1-D-only scope of the meter |
| OTOC signal as coherent interference of many small paths | constructive interference at the edge of ergodicity | Abanin et al. (Google), Nature 646, 825 (2025) | Type A mechanism run forward; a δ-cut destroys the pooling |

Bottom line (placement §13): every *operation* is standard. What is Joey's and not found published in this form: the one vocabulary across
truncations; the fragmentation/compaction reading of transpilation variants and the fewest-`max_paulis` rule; the cancellation-residue reason
for abstaining on a contradicted sign; the non-detect rule imported into circuit simulation; the regime-dependent α (Currie's LOD/LOQ
regimes turned into an estimator switch). Overstated in the corpus and to be fixed in any paper: "N = N* self-adjoint" for the scalar
operator; "N ≡ st()" (st is additive, N is not — proved `rfl` only because st was defined as N); "spectral gap enforced/derived" (it is imposed
by the cutoff); "unitarity" for N + R = id; ejection/toroid/wormhole theorems described as physics when the Lean content is `ring`.
References with full bibliographic detail, and the dagger marks on those not re-verified online, are in `placement.md`.

---

## 5. The Lean sketch

`C:/Users/jmess/otoc_audit/mnf2_synth/MNF_Injection_Ejection.lean` — **unverified; never compiled** (no toolchain here; pinned environment for the
Ubuntu session: `leanprover/lean4:v4.24.0`, Mathlib `f897ebcf`, per `mnf2_package/README_HANDOFF.md`). Self-contained: it re-declares the Core
definitions verbatim (the corpus files import nothing from each other) and tags every item `[CORPUS]` or `[PROPOSED]`. Contents:

* §0 core copies: `nullify`, `remainder`, `NorthProbe`, `SouthProbe`, `IsEjectionThreshold`, `IsReservoir`, `Gapped`; `conservation` (copied
  proof), `idempotent'` without the superfluous `0 ≤ Δ`.
* §1 the two missing core laws: `dilation_covariance`, `abs_nullify_antitone_in_threshold` (the correct two-sided Δ-monotonicity).
* §2 ejection and deficit: `eject`, `deficit`; `eject_gapped`, `eject_idem`, `nullify_eject`, `eject_nullify`, `remainder_eject`, `eject_sub_nullify`
  (gap jump), `eject_probe_reading` (the corpus predicate as an identity), `eject_dilation`, `nullify_comp_nullify`, `eject_comp_eject`,
  `nullify_floor`, `eject_ceiling` (the adjunction), `deficit_deficit`, `deficit_tripotent`, `nullify_deficit`, `northProbe_deficit` (probe swap),
  `eject_eq_id_add_deficit`; `metricProj`, `metricProj_branch`, `metricProj_deficit_swap`.
* §3 representations: `Rep := List ℝ`, `content`, `nu`, `hidden`, `eps`, `SameSign`; `rep_conservation` (general list conservation, induction
  attempt), `rep_not_distributive`.
* §4 injection: `inject`, `compact`, `refine`, `kstar`; `content_inject`, `nu_inject` (ν_Δ∘I_k = N_{kΔ}), `eps_inject`, `inject_nullified`,
  `inject_at_kstar`, `eventual_nullification`, `typeA_on_demand`, `compact_inject`, `nullify_sees_through`, `refine_inject`.
* §5 cascades: `cascade`, `ladder_not_composite`, `deltaStar` (as `sSup`), `deltaStar_singleton`, `nu_eq_zero_of_all_below`, `deltaStar_inject`,
  `sameSign_refine_le`, `sameSign_nu_le_content`, `sameSign_sign`, `mixed_refine_can_increase`, `zero_reading_uninformative`; in-process vs post-hoc:
  `inProcessStep`, `inProcess`, `postHoc`, `inProcess_ne_postHoc` (the two-coordinate witness).
* §6 residue and gate: `residue`, `residue_eq`, `two_piece_sign_safe`, `residue_both_signs`, `realise`, `signGate`, `gate_minimax`.
* §7 soft gates: `softGate`, `softNullify`, `soft_idem_iff`, `soft_no_gap`, `hardGate_is_nullify`.
* §8 the additive value-level pair from the catalogue (`injectAdd`, `ejectAdd`) with its conservation, for completeness.

Census (grep, 2026-11-03): 31 definitions, 56 theorem statements, 44 `sorry` lines; 18 theorems carry a complete proof attempt
(`conservation`, `idempotent'`, `dilation_covariance`, `abs_nullify_antitone_in_threshold`, `eject_probe_reading`, `nullify_floor`,
`northProbe_deficit`, `eject_eq_id_add_deficit`, `nullify_eq_id_sub_deficit_sq`, `rep_conservation`, `content_inject`, `inject_nullified`,
`compact_inject`, `nullify_sees_through`, `ladder_not_composite`, `residue_eq`, `hardGate_is_nullify`, `injectAdd_ejectAdd`); the other 38 are
`sorry` with the intended argument in a comment, and a few of the attempted ones depend on `sorry`'d lemmas (`inject_nullified` on `nu_inject`,
`nullify_eq_id_sub_deficit_sq` on `deficit_deficit`, `ladder_not_composite` on `nullify_comp_nullify`). The handoff asks the Ubuntu session to
report which definitions elaborate, which theorems close, and the goal state at each failure; the statements, not the proofs, are the deliverable.

---

## 6. Open questions and the next experiments

**Formal.**
1. The two-sided Δ-monotonicity should be adopted as |N_{Δ₂}x| ≤ |N_{Δ₁}x| (Δ₁ ≤ Δ₂); the ℕ statement is false on ℝ for x < 0, and nobody has
   written the correct one. (Sketch §1.)
2. Which point is the ejection locus — the band edge x = Δ (`IsEjectionThreshold`) or the band centre Δ/2 (`north_probe_zero_iff`)? The wormhole
   files use both. The metric-projection reading says: the centre is where the decision switches, the edge is where E lands. A gap at Δ/2 on
   the probe value would be needed for the RH-style squeeze to transfer, and no file assumes it.
3. A **time-indexed cascade** is the missing object: the lab's 25/25 result (in-process more confining than post-hoc) is not expressible with ν
   on a final partition. The sketch's `inProcess`/`postHoc` is the first definition; wanted are statements of the form "in-process reading = 0
   while post-hoc ≠ 0 with the content's sign" under an assumption on the dynamics (e.g. a splitting step followed by a merging step), and a
   bound relating δ* to the bottleneck (the observed δ* ≈ b/7 with a stable offset, IQR width 0.7 in log₂, is unexplained).
4. Signed injection: injecting −ε into a +0.0e pool can produce a false ground (`mixed_can_cancel`), one-signed injection cannot
   (`one_sided_sum_zero_iff`). The gate theorem is formalised on readings; a magnitude-preserving version is open (sign-only lost: 54 vs 118).
5. Full realisability shows readings carry no information without a structural assumption on the fragmentation. What is the weakest assumption
   (bounded piece count? same-sign pieces? `max_paulis` as a refinement proxy?) under which a coherent single reading is provably informative,
   matching v7 118 vs v8 56?
6. Is there a lattice on representations (refinement order) on which ν_Δ is a kernel operator with a right adjoint ("coarsest representation
   with a given reading")? The adjunction E ⊣ i ⊣ N is only on the half-line.
7. Dilation covariance and the three-class truncation of `nullification_holographic.py` are the only pieces of the framework the solver code
   executes; both should be written as Lean definitions/theorems (dilation covariance is in the sketch).
8. The corrected Type A (Batch4_3) makes z independent and says nothing about N; the original two-argument Type A (= non-distributivity) is
   the one the data use. The Ξ-baryon instance should be dropped.
9. H_N entropy: the compilation claims a formally verified nullification-aware entropy; none exists in the 301 files. Either it is elsewhere or
   the claim belongs in the corrections log.
10. A compile pass on the clean subset (Core, Batch4_2, MNFmeetsDavisSet4, Batch17, output56, Batch12 aristotle, Nullification_Aristotle_Extension)
    would settle which "proved" entries are real; eight mojibake files and the false-instance files are known not to compile as on disk.

**Experiments (all local, no credits).**
1. **Canonical δ*.** Compute δ* of the fixed-basis Pauli expansion of ⟨Z_q⟩ for S3 with `twopt/pp2.py` at an absolute threshold, to test whether
   δ*(ρ_canonical) is a circuit property (and whether BlueQubit's internal threshold is absolute or relative to the largest coefficient —
   the two readings predict the same sign of the fragmentation effect but different magnitudes).
2. **Quantitative mixed-sign refinement.** Bound |res_Δ| by the dropped weight Σ_{|p_i|<Δ}|p_i| and test it against the S3 shrink/overshoot ratios
   (0.64–1.37).
3. **K-sweep of the pool decomposition.** The type-A window, accumulation factor and residue |Σp|/Σ|p| were measured at one split depth per ID;
   a K-sweep on a few IDs tells whether the residue–|truth| relation (ρ +0.92) is K-invariant.
4. **1-D Pauli-path ladders with truth** (S2 is on disk) to see whether the ~0.4 ejection reading is a 2-D/depth property or generic.
5. **2-D Bloch probe at χ ≥ 64–128** (no such data on disk) to see whether |r| becomes contracting in 2-D beyond the floating-point-chaos regime.
6. **Midpoint estimator.** The metric projection suggests rounding reservoir values to 0 or Δ by the sign of x − Δ/2; every hard variant cut real
   signal in the emulator, so it is expected to fail, but it has not been run.
7. **Iterated soft gate.** A gate with the witness updated along with x (fixed-point shrinkage rather than one-shot) — not tried, not pre-registered.
8. **Injection across sites** (the OTOC map's "pool across neighbours", inventory D5): untested on data and undefined in the corpus.

---

## Appendix: files

* This synthesis: `C:/Users/jmess/otoc_audit/mnf2_synth/MNF_beyond_projection.md`, `MNF_Injection_Ejection.lean`, `check_synth.py`.
* Sources (read-only): `mnf2_formal/catalogue.md` (+ `_extract/`), `mnf2_algebra/algebra.md`, `mnf_ops.py`, `worked_examples.py`, `draws.json`,
  `S3_truth.json`; `mnf2_lab/results.md` (+ scripts, `*.json`, `fig_s3_cascade.png`, `fig_bloch_cascade.png`, logs); `mnf2_lit/placement.md`;
  `mnf2_package/README_HANDOFF.md`, `build_package.sh`.
* Hackathon record: `C:/Users/jmess/Downloads/otoc_hack/otoc_hack/STATUS.md` (closing summary), `ALL_NOTES.md`, `SUBMISSION_LOG.md`;
  Oct-24 inventory `C:/Users/jmess/otoc_audit/mnf_inventory/inventory.md`; OTOC map `explore/MNF_x_OTOC_map.md`.
* Corpus: `C:/Users/jmess/Downloads/nullification_cascade_lean/files/` (301 files), `MNF_Bridge78.lean`, `mnf_wormhole_nsa_merged.lean`,
  `MNF_Complete_Compilation_and_Corrections.md`, the two PDFs, the docx, the four solver scripts and the quimb notebook.
