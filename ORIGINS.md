# Origins of the nullification operator

How the operator in this library came to be what it is. Each step names the earliest file
found that carries it. Dates are file dates from Joey's phone and laptop downloads, or a
record's own date. Documents marked *(in `origins/`)* are copied into this repository as
downloaded; the others are cited by title and DOI. None of the early documents is a claim of
this library: where they say more than the Lean files prove, the Lean files and
[DEPOSIT_MAP.md](DEPOSIT_MAP.md) are what stands.

## Two different objects carry the name

The name *nullification operator* has meant two mathematically different things:

1. **The projection form (2025).** A linear operator N on a Hilbert space with N² = N and
   N† = N, which keeps a chosen subspace and sends its complement to 0. N = ∏ⱼ Pⱼ, a product
   of projections, or N = I − P. This is an orthogonal projection.
2. **The threshold form (December 2025 →).** A scalar map that keeps a value at or above a
   threshold and sends it to 0 below:
   `N(Δ, x) = x if Δ ≤ x, else 0`, with remainder `R(Δ, x)`, so that N + R = id. The values
   fall into three classes: [0] (x = 0), [0.0e] (0 < x < Δ, the reservoir) and [1] (Δ ≤ x,
   observable).

The threshold form is idempotent, like a projection, but it is not linear:
`N(Δ, x + y) ≠ N(Δ, x) + N(Δ, y)` in general. Batch 3, *Distributivity*, proves exactly this
non-distributivity. **Every Lean file in this library formalizes the threshold form.** The
projection form survives as motivation, and as the vocabulary of "projecting out" the reservoir.
The MNF2 extension ([`extension/`](extension/)) is the systematic study of what the threshold
form does that a projector does not (ejection, injection, cascades).

## Timeline

| date | step | source |
|---|---|---|
| 2025-03-18 | First use of *nullification*: "quark nullification (∞ / ∧ = 0)", an informal device in a Yang–Mills / IBM-hardware collaboration with Grok 3. Physics, no definition | `null.tex`, *Exploring the Yang-Mills Mass Gap: Nullification as the Key* (phone download; not copied) |
| 2025-06-23 | Public circuits repository | [Joeyxyxyz/Yang-Mills-Nullification-Circuits](https://github.com/Joeyxyxyz/Yang-Mills-Nullification-Circuits) |
| 2025-07-02 | **The name "Messina Nullification Framework"**; the nullification operator N = ∏ⱼ Pⱼ and the "0.0e continuum" | *Universal Gauge Theory Mass Gaps: The Messina Nullification Framework…*, Zenodo [10.5281/zenodo.15763702](https://doi.org/10.5281/zenodo.15763702) (with Grok 3 and Claude) |
| 2025-07-04 | **First mathematical definition** (projection form): Definition 2.1, N² = N, N† = N, selective action on a subspace S; N = Σᵢ \|ψᵢ⟩⟨ψᵢ\|; σ(N) ⊆ {0, 1}; Tr N = dim S | *The Nullification Operator: Mathematical Foundation and Elementary Applications* *(in `origins/2025-07_operator-as-projection/`)* |
| 2025-10 | N = I − P; idempotence, hermiticity, gauge covariance | *Gluonic Isolation via the Nullification Operator*, Zenodo 17370031 (cited from `origins/FRAMEWORK_DEVELOPMENT_TIMELINE.md`) |
| 2025-12-24 | **The three classes** [1] (survives), [0] (true zero), [0.0e] (operationally zero); spectral gaps by construction σ(NAN) = {0} ∪ [Δ, ∞); quotient V/ker N | *The Nullification Operator: A Universal Algebraic Framework for Spectral Decomposition* *(in `origins/2025-12_three-classes/`)*; Zenodo 18077944, *The Nullification Operator: Algebraic Core* (N(x) + R(x) = x, three-valued classification, correspondence with Robinson's standard part st()) |
| 2025-12-31 | **First Lean** and the switch to the threshold form: `nullify Δ x := if x >= Δ then x else 0`, `remainder`; `conservation`, `idempotent`, `spectral_gap` (output is 0 or ≥ Δ), `remainder_bound`, non-linearity | `Nullification_Simple_Proof.lean` *(in `origins/2025-12-31_first-lean/`)* |
| 2026-01-28 | **Batches 1–5 with Aristotle** (Harmonic), 50 theorems on ℕ: classification and remainder, monotonicity and composition (R∘N = 0, N∘R = 0), distributivity, a Yang–Mills numerical example, image and fixed points | `Batch1_Classification.lean` … `Batch5_Image.lean` *(in `origins/2026-01_aristotle-batches/`)*; plan in `Nullification_Framework_Roadmap.md` (2026-01-14) |
| 2026-02 | The two-sided real form `nullify Δ x := if \|x\| ≥ Δ then x else 0` (`Nullification_Core.lean`); the RH line, output28–86: SpectralGap, probes, leveling theorem, signed multiplicity, Speiser and Fischer-forward paths; Sturm–Liouville via Aristotle | corpus files (Windows laptop, `nullification_cascade_lean/files/`, 301 files); census in `origins/CORPUS_CATALOGUE_2026-11-01.md` §0 |
| 2026-03 | AFM submission, *Sturm–Liouville Eigenvalue Simplicity and a Spectral Assumption Interface in Lean 4* (v1–v7); MNF v3 **Vol. 1 Core Operator Library** and **Vol. 2 RH** | [Joeyxyxyz/MessinaNullificationFramework_RH_AFM](https://github.com/Joeyxyxyz/MessinaNullificationFramework_RH_AFM); Zenodo [18902403](https://doi.org/10.5281/zenodo.18902403), [18902325](https://doi.org/10.5281/zenodo.18902325) |
| 2026-10-27 | **Consolidation.** The operator core re-proved without `native_decide` as `MNFCore` (Lean 4.28.0, no Mathlib); the RH files consolidated into `MNF.RH`; the false axiom `func_eq_deriv`, the unsupported Levinson–Montgomery axiom and the placeholder-function statements withdrawn; the "master theorem" RH ⟺ gap made unconditional | [`core/`](core/), [`docs/notes/MNF_Build_Review_2026-10-27.md`](docs/notes/MNF_Build_Review_2026-10-27.md), [DEPOSIT_MAP.md](DEPOSIT_MAP.md) §5 |
| 2026-10-27 → 11-11 | **Eleven Comparator runs** with receipts: OpenAI's 7/8 theorem and zeta23 (PASS), then MNF.RH v1–v3, MNF on zeta23, the density layer v2–v6 (ACCEPTED) | [VERIFICATION.md](VERIFICATION.md) |
| 2026-11-01/03 | **MNF2, beyond projection.** A catalogue of every operation the corpus defines beyond N, then the injection/ejection algebra, 56 theorems | [`origins/CORPUS_CATALOGUE_2026-11-01.md`](origins/CORPUS_CATALOGUE_2026-11-01.md), [`extension/`](extension/) |

## What the corpus looked like before consolidation

`origins/CORPUS_CATALOGUE_2026-11-01.md` read all 301 corpus files. Its findings:

- The threshold operator is re-declared about 100 times, under ten names (`N`, `nullify`,
  `N_nat`, `nullifyR`, `nullifyNorm`, `nullifyBloch`, …), in six carrier types.
- The three-class enum is re-invented at least ten times.
- Every file stands alone. 57 files use the one-sided ℕ form and 40 the two-sided ℝ form;
  three use a one-sided real form that disagrees with the core for x < 0.
- In one file (`MdBatch1.lean`) N is the identity, which makes that file's "nullification"
  theorems vacuous.

This is why the library has one `MNFCore` and one `MNF.RH` instead of the corpus files. It is
also why the deposit map tells anyone re-depositing corpus material to check each file for
three patterns: a hypothesis typed as `True`, a `Classical.choice` placeholder, and a
conclusion of the form `… → True`.

## What is not here

- The 301-file corpus itself. It is on the Windows laptop; the Lean 4.24.0 AFM subset is in
  the AFM repository.
- The physical-application volumes (Vol. 3), the IBM circuit runs and their mass-gap numbers.
  Those are physics claims and outside this library.
