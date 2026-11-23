# MNF RH Frontier Package — what is left, as Lean goals

Bundle 2 (`bundle2_afm_core`, Lean 4.24.0 / Mathlib f897ebcf) now has two new files:

| file | theorems | axioms |
|---|---|---|
| `MNF/RH/Reduction.lean` | 12 | propext, Classical.choice, Quot.sound |
| `MNF/RH/Schrodinger.lean` | 8 | propext, Classical.choice, Quot.sound |

`lake build && lake env lean Audit.lean` now prints 59 `#print axioms` lines, all standard.
No `sorry`, no custom axiom, 0 warnings in the two new files.

The package does not prove RH. It does something narrower and useful: it takes every
"attack" idea in the corpus — the gap, "a multiple zero kills the gap", Hilbert–Pólya,
Sturm–Liouville simplicity, the τ-line probes, "every other zero" — and rewrites each as
an `↔` or a structure, so the remaining content is one named Lean goal rather than a
family of restatements.

## 1. The gap is a zero-free band (`Reduction.lean` §1)

```
gap_iff_zeroFreeBand (Δ) : SpectralGapHyp Δ ↔ ZeroFreeBand Δ
ZeroFreeBand Δ := ∀ ρ, is_nontrivial_zero ρ → ρ.re ≤ 1/2 ∨ 1/2 + Δ ≤ ρ.re
```

A gap at Δ is literally "no zero in the open band `1/2 < Re ρ < 1/2 + Δ`". Nothing about
nullification, dilation or the operator survives the `↔`.

**"Every other zero"** — made precise and proved:

```
gap_of_right_side : (∀ ρ, is_nontrivial_zero ρ → 1/2 < ρ.re → 1/2 + Δ ≤ ρ.re) → SpectralGapHyp Δ
```

It is enough to kill the zeros on the right of the line; the left ones follow from
`ρ ↦ 1 − ρ`. So the τ-line construction only ever has to handle one side of each
reflected pair. Combined with the 7/8 result:

```
rh_of_band_of_zeroFree (hθ : ZeroFreeRightOf θ)
    (h : ∀ ρ, is_nontrivial_zero ρ → 1/2 < ρ.re → θ < ρ.re) : RiemannHypothesis
```

With θ = 7/8: **RH is exactly "no zero with `1/2 < Re ρ ≤ 7/8`"**. That closed band is
the entire remaining target. Any mechanism that does not reach *every* point of it does
nothing (`gap_below_bound_insufficient`, Gap.lean).

## 2. "A multiple zero kills the gap" (`Reduction.lean` §2)

```
multipleZeroKillsGap_iff : MultipleZeroKillsGap ↔ (RiemannHypothesis → AllZerosSimple)
fischerForward_iff      : FischerForward      ↔ (RiemannHypothesis → AllZerosSimple)
```

Both corpus hypotheses are the simple-zeros conjecture under RH, word for word. They
are not a route *to* RH (they assume it), and they cannot be discharged by anything
about gaps because the gap side of each `↔` is RH itself.

## 3. Hilbert–Pólya without an operator (`Reduction.lean` §3)

```
rh_of_realSpectrumRealization (Λ : Set ℝ) :
  (∀ ρ, is_nontrivial_zero ρ → ∃ l ∈ Λ, (l:ℂ) = (ρ − 1/2)/i) → RiemannHypothesis
```

The Hilbert–Pólya step needs no self-adjointness, no Hilbert space, no spectral theorem:
if the numbers `(ρ − 1/2)/i` are real, `Re ρ = 1/2`. The operator's only job is to make
them real. `rh_of_symmetric_operator` (Hypotheses.lean) is this with
`Λ = eigenvalues of a symmetric T`.

## 4. The Schrödinger bridge, with Sturm–Liouville attached (`Schrodinger.lean`)

```
structure SchrodingerRealization where
  V            : ℝ → ℝ
  confining    : IsConfiningPotential V
  level        : ℂ → ℝ
  eigenfunction: ℂ → (ℝ → ℝ)
  realizes     : ∀ ρ, is_nontrivial_zero ρ → IsSturmLiouvilleEigenfunction V (level ρ) (eigenfunction ρ)
  dictionary   : ∀ ρ, is_nontrivial_zero ρ → ((level ρ):ℂ) = (ρ − 1/2)/i
```

* `rh_of_realization R : RiemannHypothesis` — Hilbert–Pólya through a confining
  Schrödinger operator `−d²/dx² + V`.
* `eigenvalue_simple_of_realization R ρ : IsSimpleEigenvalue R.V (R.level ρ)` — **this is
  where the Sturm–Liouville theorem finally does work**: once a realization exists, every
  level is a simple eigenvalue, for free.
* `allZerosSimple_of_realization R (hd : MultiplicityDictionary R) : AllZerosSimple` —
  but passing from "simple eigenvalue" to "simple zero of ζ" needs a dictionary between
  spectral multiplicity and `zeta_order`, and `multiplicityDictionary_iff` shows that
  dictionary is *equivalent* to the simple-zeros conjecture. SL simplicity does not
  shortcut it.
* `realization_forces_line` — the `dictionary` field alone forces `Re ρ = 1/2`. So there
  is no soft part of the structure to fill in first: constructing `V` with the right
  spectrum is the same task as RH, as expected for any Hilbert–Pólya operator.

## 5. What a gap mechanism must deliver (`Reduction.lean` §4)

```
structure GapMechanism (Δ) where
  P : ℂ → Prop
  band_zero_satisfies : ∀ ρ, is_nontrivial_zero ρ → 1/2 < ρ.re → ρ.re < 1/2 + Δ → P ρ
  refuted : ∀ s, ¬ P s
gap_of_mechanism : GapMechanism Δ → SpectralGapHyp Δ
mechanism_of_gap : SpectralGapHyp Δ → Nonempty (GapMechanism Δ)
```

A "mechanism" is any property that every band zero would have and that nothing has.
Having one is equivalent to having the band, so looking for a mechanism is not a
weaker problem than looking for the zero-free band — it is the same problem renamed.
This is the precise form of the DEPOSIT_MAP remark that the gap route "is RH restated".

## 6. The τ-line probes (`Reduction.lean` §4, end)

```
NorthProbe ρ := ρ.re − 1/2        SouthProbe ρ := −(ρ.re − 1/2)
probe_balance  : NorthProbe ρ + SouthProbe ρ = 0          -- for every ρ ∈ ℂ
probe_reflect  : NorthProbe (1 − ρ) = SouthProbe ρ
probes_zero_iff: NorthProbe ρ = 0 ∧ SouthProbe ρ = 0 ↔ ρ.re = 1/2
```

The leveling identity at τ/4 and 3τ/4 holds for every complex number, not just zeros, so
it is definitional and constrains nothing. "Both probes read zero" is `Re ρ = 1/2`
verbatim. A τ-line argument would have to produce a property that fails for an
off-line zero and that ζ actually has — i.e. a `GapMechanism`.

## Where a push could still go

Everything above is `↔`-tight, so the only non-circular targets are:

1. **The band `1/2 < Re ρ ≤ 7/8`**, one side only (`gap_of_right_side`), reached by an
   argument about ζ, not about the shifted set. Known zero-free regions
   (de la Vallée Poussin, Vinogradov–Korobov) shave `Re ρ > 1 − c/log|t|^{2/3}…`, never a
   fixed band; a fixed band of any positive width is RH-grade.
2. **A `SchrodingerRealization`** — an explicit confining `V`. The Berry–Keating /
   Connes programmes are attempts at exactly this field-by-field; none is a theorem.
3. **Nothing on the multiplicity side**: with or without SL, "simple zeros" is a separate
   conjecture (`multiplicityDictionary_iff`), not a consequence of RH.

Anything else proposed for the corpus can be checked against this file by asking: which
of `GapMechanism`, `ZeroFreeBand`, `SchrodingerRealization` does it construct?
