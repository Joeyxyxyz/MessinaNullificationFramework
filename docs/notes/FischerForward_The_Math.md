# Fischer Forward — the math

Companion note to `MultipleZeroKillsGap_Report.docx` and `PathD_Degeneracy_Report.docx`
(Feb 12, 2026) and to `output56_PathD_ConfinementChiral.lean` / `output56_PathD_v2.lean`.
Written 2026-10-28 against the kernel-checked library `MNF/RH/{Core,Gap,Hypotheses,Reduction}.lean`
(Lean 4.24.0 / Mathlib f897ebcf; also accepted by Comparator at the OpenAI pin, receipt
`qrh-mnf-receipt`, status ACCEPTED). Everything marked **[PROVED]** below was checked by the
Lean kernel on the standard three axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 1. The objects

All on the Mathlib `riemannZeta`.

| symbol | definition | file |
|---|---|---|
| `is_nontrivial_zero ρ` | `ζ(ρ) = 0 ∧ 0 < Re ρ < 1` | Core |
| `zeta_order ρ` | `(analyticOrderAt riemannZeta ρ).toNat` — the multiplicity of the zero | Core |
| `AllZerosSimple` | `∀ ρ, is_nontrivial_zero ρ → zeta_order ρ = 1` | Core |
| `DerivativeNonvanishing` | `∀ ρ, is_nontrivial_zero ρ → ζ'(ρ) ≠ 0` | Core |
| `ShiftedZeroSpectrum` | `{ Re ρ − 1/2 : ρ a nontrivial zero } ⊆ ℝ` | Core |
| `SpectralGapProperty S Δ` | `∀ x ∈ S, x = 0 ∨ |x| ≥ Δ` | Gap |
| `SpectralGapHyp Δ` | `SpectralGapProperty ShiftedZeroSpectrum Δ` | Hypotheses |
| `FischerForward` | `SpectralGapHyp (1/2) → DerivativeNonvanishing` | Reduction |
| `MultipleZeroKillsGap` | `∀ ρ, is_nontrivial_zero ρ → 2 ≤ zeta_order ρ → ¬ SpectralGapHyp (1/2)` | Reduction |

The two "Fischer" hypotheses are the February definitions verbatim (output56 §2–3), with
`is_multiple_zero ρ` unfolded to `2 ≤ zeta_order ρ`.

## 2. What the February chain proved, and what it did not

The Feb 12 report lists five theorems. Their present status:

| Feb 12 claim | status now | where |
|---|---|---|
| T1 `SpectralGapProperty → RH` | **[PROVED]**, and strengthened to an `↔`: `RiemannHypothesis ↔ SpectralGapHyp Δ` for every `Δ ≥ 1/2` | `riemannHypothesis_iff_gap_half` (Gap) |
| T2 `SpectralGap + FischerForward → RH ∧ AllZerosSimple` | **[PROVED]** — but see §3: with T1 as an `↔` it is `RH + (RH → simple) → RH ∧ simple`, i.e. modus ponens | assemble from `rh_of_gap`, `allZerosSimple_iff_derivativeNonvanishing` |
| T3 `MultipleZeroKillsGap → FischerForward` | **[PROVED]** (February's proof had an `exact?` hole; the implication now follows from `multipleZeroKillsGap_iff` and `fischerForward_iff`, both `↔` the same proposition) | Reduction |
| T4 `order = 1 ↔ ζ'(ρ) ≠ 0` | **[PROVED]** from Mathlib's analytic-order theory, no hypothesis | `order_one_iff_deriv` (Core) |
| T5 "GUE level repulsion" | not in the library; February's statement was about a 2×2 model matrix, not ζ | — |

So the chain is intact and now hole-free. The question is what it says.

## 3. The reduction **[PROVED]**

```
fischerForward_iff      : FischerForward      ↔ (RiemannHypothesis → AllZerosSimple)
multipleZeroKillsGap_iff: MultipleZeroKillsGap ↔ (RiemannHypothesis → AllZerosSimple)
```

Proof sketch (both directions are a few lines in `Reduction.lean`):

* `ShiftedZeroSpectrum ⊆ (−1/2, 1/2)` because every nontrivial zero has `0 < Re ρ < 1`
  (`shifted_bounded`). So a gap of width `1/2` leaves only the point `0`: the gap at `1/2`
  is literally "every nontrivial zero has `Re ρ = 1/2`", which is RH
  (`riemannHypothesis_iff_strip`, from Mathlib's `RiemannHypothesis`).
* Hence `SpectralGapHyp (1/2) → DerivativeNonvanishing` is `RH → DerivativeNonvanishing`,
  and `DerivativeNonvanishing ↔ AllZerosSimple` by T4.
* `MultipleZeroKillsGap` is the contrapositive of the same statement.

**Reading.** `FischerForward` is the *simple-zeros conjecture under RH*. It contains no
operator, no lattice, no gap in any physical spectrum. Its hypothesis is RH itself.

Two consequences:

1. **It is not a route to RH.** T2 reads `RH ∧ (RH → simple) → RH ∧ simple`. The first
   conjunct of the conclusion is the first hypothesis. Nothing is gained toward RH; what T2
   actually says is "RH and the simple-zeros conjecture together give RH and the
   simple-zeros conjecture."
2. **No experiment can bear on it.** A proposition of the form `RH → AllZerosSimple` has no
   free parameter that a measurement could set. The lattice correlator ⟨Z_k Z_{k+8}⟩ does not
   appear in it, and no bridge theorem in the corpus connects the lattice Hamiltonian
   `H_gauge` to `riemannZeta`. The February dictionary (confinement ↔ `SpectralGapHyp (1/2)`,
   χSB ↔ `ζ' ≠ 0`) is a *naming* of two unrelated propositions with the same shape; it is
   not a theorem and, by `fischerForward_iff`, cannot become one without first proving RH.

## 4. What the February "activation" step actually did

§5.2 of the report argues: *MultipleZeroKillsGap is empirically supported ⟹ (by T3)
FischerForward ⟹ (by T2) RH ∧ AllZerosSimple.* Three separate problems:

* **Direction.** T3 is `MultipleZeroKillsGap → FischerForward`. Support for the premise
  would be needed; the premise is `RH → AllZerosSimple` (§3), which the experiment does not
  measure.
* **Translation.** `2 ≤ zeta_order ρ` is a statement about the multiplicity of a zero of ζ.
  The experiment forces two qubit components into the same state by a CNOT. These are not
  the same object, and no theorem in the corpus maps one to the other.
* **Hypothesis in the conclusion.** Even granting both, T2 still needs `SpectralGapHyp (1/2)`
  as a *separate* input — and that input is RH. "Observed confinement" on a 2×4 lattice is
  not `SpectralGapHyp (1/2)`.

None of this is a criticism of the measurement. It is a statement about the Lean chain the
measurement was attached to.

## 5. What the experiment did establish

Keep it; cite it as what it is.

* **System:** 64-qubit circuit, 2×4 lattice, 8 gauge components per site, pure-gauge
  Hamiltonian (fermion sector excluded), 16 measured qubits, 48-qubit unmeasured bath.
* **Design:** three variants differing only in step 1.5 — C0 (none, 208 CX), C0b
  (self-cancelling CNOT pairs, 248 CX, *more* noise than C3), C3 (state-copying CNOTs,
  224 CX). The depth-matched control is the right control.
* **Observable:** ⟨Z_k Z_{k+8}⟩ between sites (0,0) and (1,0), noise floor ≈ 0.011 at
  8,061 shots.
* **Result:** on the four *untouched* components, C0b → C3 drops 0.0888 → 0.0693
  (−22.0%); 5,000/5,000 bootstrap resamples agree; 95% CI of the difference
  [0.0113, 0.0253]; forced-vs-free asymmetry P = 99.98%. 112,854 shots, 14 runs, three
  backends.

**Honest statement of the finding:** *in this lattice model, forcing pairwise degeneracy of
gauge components before Hamiltonian evolution suppresses the nearest-site Z–Z correlator on
components that received no extra gates, by an amount that a depth-matched noise control does
not reproduce.* That is a result about a confining lattice gauge simulation and belongs with
the Yang–Mills / Bundle 1 material (where `N` removing the fermion sector is the
nullification operator doing real work). It says nothing about ζ.

Open points that are the experiment's own, not RH's: whether CNOT-before-evolution
degeneracy is "healed" by the plaquette terms (the PathD report's question to Grok); a CRX(θ)
sweep; a degeneracy operator that commutes with `H_gauge`.

## 6. How to cite it in the deposit

Suggested wording for the Zenodo README / DEPOSIT_MAP:

> **MultipleZeroKillsGap experiment (Feb 2026).** A 64-qubit IBM run showing that forced
> component degeneracy suppresses the confinement correlator in a 2×4 pure-gauge lattice
> model (−22% on untouched components vs. a depth-matched control, P > 99.99%). Filed under
> lattice gauge / Yang–Mills. The accompanying Lean hypotheses `FischerForward` and
> `MultipleZeroKillsGap` are each kernel-equivalent to "RH ⟹ all zeros simple"
> (`fischerForward_iff`, `multipleZeroKillsGap_iff`, MNF/RH/Reduction.lean), so the
> experiment is **not** evidence for or against RH and is not cited as such.

## 7. If the Fischer idea is to touch ζ at all

The only non-circular version is the Schrödinger bridge in `MNF/RH/Schrodinger.lean`: a
confining potential `V` whose `L²` eigenlevels are `(ρ − 1/2)/i`. There the Sturm–Liouville
theorem does give "every level is simple" for free (`eigenvalue_simple_of_realization`),
which is the one place a Fischer-style "confinement ⟹ non-degenerate spectrum" statement is a
theorem rather than a name. But `multiplicityDictionary_iff` shows the step from "simple
level" to "simple zero of ζ" is again exactly the simple-zeros conjecture. The lattice
experiment is about a 64-qubit `H_gauge`, not about any such `V`.

---

### References (literature the February files cite)

* R. Alkofer, C. S. Fischer, F. J. Llanes-Estrada, "Dynamically induced scalar quark
  confinement," Mod. Phys. Lett. A 23 (2008); arXiv:hep-ph/0607293.
* G. Eichmann, C. S. Fischer, W. Heupel, "The light scalar mesons as tetraquarks,"
  Phys. Lett. B 753 (2016); arXiv:1508.07178.
* E. Klempt, "Scalar mesons and the fragmented glueball," Phys. Lett. B 820 (2021);
  arXiv:2104.09922.
* T. J. Allen, M. G. Olsson, S. Veseli, "From scalar to string confinement,"
  Phys. Rev. D 62 (2000); arXiv:hep-ph/0001227.
* Mathlib: `RiemannHypothesis`, `riemannZeta_one_sub`, `analyticOrderAt`.
