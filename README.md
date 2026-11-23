# The Messina Nullification Framework (MNF) — Lean library

Joey Messina. The mathematical part of the Messina Nullification Framework, gathered in one
place: the nullification operator and its algebra, the `MNF.RH` library that applies it to the
zeros of the Riemann zeta function, the injection/ejection extension, and the density layer on
the zeta23 tree. Every Lean file here is the one that was judged, byte-for-byte, and the
Comparator receipts are next to it.

Physical applications (IBM circuits, Yang–Mills lattice runs, battery chemistry, optics,
black holes) are **not** in this repository. Only the math is.

> **What this library does and does not do.** It formalizes the nullification operator and
> proves, in Lean, exactly how the MNF gap hypothesis relates to the Riemann hypothesis: the
> two are equivalent for every Δ ≥ 1/2 (from Mathlib alone), and for every Δ > 3/8 given
> OpenAI's 7/8 zero-free theorem. It also formalizes classical analytic results (Bohr–Landau
> 1914, a Carlson-type zero-density estimate, the absence of real zeros of ζ in (0, 1)). It
> does **not** prove RH, the simplicity of the zeros, or any zero-free strip next to the
> critical line. In one line, from [`DEPOSIT_MAP.md`](DEPOSIT_MAP.md) §6: *the nullification
> framework re-expresses RH; it does not reduce it.*

## The operator

The scalar threshold operator, its remainder and the three classes:

```lean
def N (Δ x : Nat) : Nat := if Δ ≤ x then x else 0        -- nullification
def R (Δ x : Nat) : Nat := if Δ ≤ x then 0 else x        -- remainder
-- classes: [0] x = 0 (true zero) · [0.0e] 0 < x < Δ (reservoir) · [1] Δ ≤ x (observable)
theorem conservation (Δ x : Nat) : N Δ x + R Δ x = x     -- N + R = id
```

On ℝ the operator is two-sided, `nullify Δ x = if Δ ≤ |x| then x else 0`
([`rh/MNF/RH/Gap.lean`](rh/MNF/RH/Gap.lean)). It is idempotent, dilation-covariant (only
x/Δ matters) and not additive. So it is a projection in the sense N∘N = N, not a linear one.
Applied to the shifted zero spectrum S = {Re ρ − 1/2}, the MNF spectral gap at Δ is the
statement "nullify is the identity on S" (`gap_iff_nullify_id`). That statement is
kernel-checked to be the zero-free strip 1/2 < Re ρ < 1/2 + Δ
(`spectralGapHyp_iff_zeroFree_strip`).

How the operator got here — from the March 2025 Yang–Mills notes, through the July 2025
projection operator N = ∏ⱼ Pⱼ and the December 2025 three-valued algebra, to the first Lean
file of 31 December 2025 — is in **[ORIGINS.md](ORIGINS.md)**.

## Layout

| folder | what | Lean / Mathlib | theorems | verification |
|---|---|---|---|---|
| [`core/`](core/) | `MNFCore`: the operator N, R, the classes, conservation, idempotence, dilation covariance over ℕ and ℚ; bit, W-state, GHZ, Hadamard, decay and two-qubit budget layers. Re-proved from Batch 1 without `native_decide` | 4.28.0, **no Mathlib** | 135 `theorem`s (307 kernel declarations audited) | built and axiom-audited (`core/audit.log`): only `propext`, `Quot.sound`, `Classical.choice`; 0 `sorryAx`, 0 `ofReduceBool`. Rebuilt from this folder 2026-11-23, audit identical. No Comparator run |
| [`extension/`](extension/) | `MNF2`: injection and ejection, beyond the projector: eject, deficit, inject/compact, cascades, soft gates (31 definitions) | 4.34.1 / `d13f23b7` | 56 | Comparator pre-check "Your solution is okay!" 2026-11-03 (Lean kernel + NanoDa, every definition body compared; `extension/comparator-precheck.log`, not a launcher receipt). The same file is receipted inside runs 7–11 on the zeta23 tree as `MNF/Extension/InjectionEjection.lean` |
| [`rh/`](rh/) | `MNF.RH` on OpenAI's tree: Core, Gap, Hypotheses, Unconditional, Counting, Reduction, Schrodinger, GapDensity + Sturm–Liouville simplicity (add-on v3) | 4.34.1 / `d13f23b7`, overlay on `openai/math@adc7f124` | 87 (41 definitions) | Comparator **ACCEPTED**, run 5, 2026-10-29 |
| [`zeta23/`](zeta23/) | the density layer on Anthropic's zeta23 tree: MNF.RH restated over zeta23, Density, Strip, ReservoirMass, Cube, InjectionEjection, Bohr–Landau closure, StripDensity (add-on v6) | 4.33.0-rc2 / `51e6992e`, overlay on `anthropics/formal-math@16a5ce41` | 534 (110 definitions) | Comparator **ACCEPTED**, run 11, 2026-11-11 (Lean kernel + NanoDa) |
| [`receipts/`](receipts/) | all eleven receipt bundles, as produced | | | sha256 of each listed in [VERIFICATION.md](VERIFICATION.md) |
| [`docs/`](docs/) | the paper *Receipted Comparator Checks…* (PDF), the frontier note, the Fischer-forward note, the corpus build review, the density ledger | | | |
| [`origins/`](origins/) | historical source documents of the operator (2025-07 → 2026-01), as downloaded; **superseded, not claims** | | | |

`rh/` and `zeta23/` are the add-ons exactly as receipted. `sha256sum -c MANIFEST.sha256` inside
each one passes. Their own `README.md`, `CLAUDE.md` and `scripts/` are the Comparator kit's
instructions for re-running the judgement.

## Register

Statuses follow the deposit map: **[PROVED]** kernel-checked from Mathlib alone; **[PROVED | 7/8]**
also uses OpenAI's 7/8 theorem; **[PROVED | this tree]** uses the receipted zeta23 library;
**[CONDITIONAL]** proved from named hypotheses; **[LITERATURE]** a published theorem stated as a
hypothesis; **[OPEN]**; **[WITHDRAWN]**. The full table of what is proved, conditional, open and
withdrawn is **[DEPOSIT_MAP.md](DEPOSIT_MAP.md)** (the current root copy, revised 2026-11-11,
reproduced verbatim). Its `notes/…` and `paper/` paths refer to the layout of
[qrh-comparator-receipts](https://github.com/Joeyxyxyz/qrh-comparator-receipts). In this repository,
the notes it cites most are in [`docs/notes/`](docs/notes/) and the paper is in [`docs/`](docs/).

Open, and not touched by anything here: `SpectralGapHyp Δ` for any Δ > 0, `AllZerosSimple`,
`SchrodingerRealization` (Hilbert–Pólya).

## Building

- `core/`: `cd core && lake build && lake env lean Audit.lean`. Lean 4.28.0, no dependencies,
  under a minute.
- `extension/`: `cd extension && lake build`. This fetches Mathlib at `d13f23b7`; use
  `lake exe cache get` first.
- `rh/`, `zeta23/`: overlays, not standalone projects. They are added onto a checkout of the
  verified upstream tree and judged by Comparator through the QRH Comparator kit. Each folder's
  README gives the steps. The kit, the add-on tarballs and the full run record are in
  [github.com/Joeyxyxyz/qrh-comparator-receipts](https://github.com/Joeyxyxyz/qrh-comparator-receipts)
  and the Zenodo record of 2026-11-11.

## Related records

- Zenodo 15763702 (2025-07-02), the framework's founding paper; Zenodo 18902403 (Vol. 1, Core
  Operator Library) and 18902325 (Vol. 2, RH), 2026-03. See [ORIGINS.md](ORIGINS.md).
- [Joeyxyxyz/MessinaNullificationFramework_RH_AFM](https://github.com/Joeyxyxyz/MessinaNullificationFramework_RH_AFM),
  the March 2026 AFM submission (Lean 4.24.0 corpus files and the v7 paper).
- [Joeyxyxyz/sturm-liouville-comparator-run](https://github.com/Joeyxyxyz/sturm-liouville-comparator-run),
  Sturm–Liouville simplicity with the first oscillation step, standalone.
- [Joeyxyxyz/qrh-comparator-receipts](https://github.com/Joeyxyxyz/qrh-comparator-receipts),
  the receipts record (kit, add-ons, receipts, paper).

## Credits and licence

Joey Messina conceived the framework, set the goals, operated every Comparator run and is
responsible for the claims. The early Lean batches were produced with Aristotle (Harmonic). The
consolidated library, the density layer, the scripts and these documents were produced with
Claude Code (Anthropic) under his direction. Comparator and lean4export are from the Lean FRO,
NanoDa is by Rob Simmons, Mathlib is by its community.

Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The upstream trees the overlays sit on
(`openai/math`, `anthropics/formal-math`) are not included here and keep their own licences.
