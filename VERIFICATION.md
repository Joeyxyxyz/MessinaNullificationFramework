# Verification

What has been machine-checked, by what, and where the evidence is. The receipts in
[`receipts/`](receipts/) are the bundles as written by the QRH Comparator kit on Joey's laptop.
Check them with `cd receipts && sha256sum -c SHA256SUMS`; each hash is also printed in
[DEPOSIT_MAP.md](DEPOSIT_MAP.md) and in the Zenodo records.

## What Comparator checks

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's proof judge. It is
given a challenge file, which holds the statements with every proof replaced by `sorry`, and a
solution. It builds both inside a sandbox, exports the proof terms with lean4export, and has the
Lean kernel re-check them (NanoDa as a second kernel where enabled). It accepts only if:

1. each claimed theorem in the solution has exactly the statement in the challenge, and every
   definition it refers to has the same body on both sides;
2. no proof uses an axiom other than `propext`, `Quot.sound` and `Classical.choice`;
3. the kernel or kernels accept the exported terms.

It does **not** check that a Lean statement matches its English description. Read the
statements. **PASS** is the kit's verdict for a cold run of an upstream tree. **ACCEPTED** is
its verdict for an add-on run on an already verified tree. Runs 6–11 were warm, cold only for
the modules each add-on introduced (DEPOSIT_MAP §10, erratum 1).

## The eleven runs

| run | label | what was judged | theorems (defs) | kernels | verdict | receipt | sha256 |
|---|---|---|---|---|---|---|---|
| 1 | `qrh-main` | OpenAI, `riemannZeta_ne_zero_of_seven_eighths_lt_re` (openai/math `adc7f124`) | 1 | Lean | **PASS** 2026-10-27, cold | `qrh-receipt.tar.gz` | `d86705398e4858e0…` |
| 2 | `zeta23-main` | Anthropic zeta23, Alpöge–Furman (anthropics/formal-math `16a5ce41`) | 17 | Lean + NanoDa | **PASS** 2026-10-28, cold | `qrh-zeta23-receipt.tar.gz` | `e0b9a4d97a04dff7…` |
| 3 | `mnf-library` | MNF.RH v1 on run 1's tree | 40 (17 as holes) | Lean | ACCEPTED 2026-10-28 | `qrh-mnf-receipt.tar.gz` | `f9180842f8c269b6…` |
| 4 | `mnf-library-v2` | MNF.RH v2, definition bodies compared | 43 (17) | Lean | ACCEPTED 2026-10-28 | `qrh-mnf-v2-receipt.tar.gz` | `c6142a402077b7f3…` |
| 5 | `mnf-library-v3` | MNF.RH v3 = [`rh/`](rh/) | 87 (41) | Lean | ACCEPTED 2026-10-29 | `qrh-mnf-v3-receipt.tar.gz` | `023d7ada93e31329…` |
| 6 | `zeta23-mnf` | MNF.RH on run 2's tree; zeta23 Theorems A–D restated | 62 (23) | Lean + NanoDa | ACCEPTED 2026-10-29 | `qrh-zeta23-mnf-receipt.tar.gz` | `1476f56809c57398…` |
| 7 | `zeta23-density` | density layer v2 | 124 (66) | Lean + NanoDa | ACCEPTED 2026-11-03 | `qrh-zeta23-density-receipt.tar.gz` | `975b21780c2c84ee…` |
| 8 | `zeta23-density-v3` | + Bohr–Landau for δ > 1/6 | 270 (76) | Lean + NanoDa | ACCEPTED 2026-11-03 | `qrh-zeta23-density-v3-receipt.tar.gz` | `0588555dccdcefcb…` |
| 9 | `zeta23-density-v4` | + Bohr–Landau for every δ > 0 | 334 (81) | Lean + NanoDa | ACCEPTED 2026-11-04 | `qrh-zeta23-density-v4-receipt.tar.gz` | `0d1919e42cbe4540…` |
| 10 | `zeta23-density-v5` | + reservoir mass, zero-density estimate | 480 (98) | Lean + NanoDa | ACCEPTED 2026-11-04 | `qrh-zeta23-density-v5-receipt.tar.gz` | `37a806b20c4ef5ab…` |
| 11 | `zeta23-density-v6` | + the strip cube, no real zeros in (0, 1) = [`zeta23/`](zeta23/) | 534 (110) | Lean + NanoDa | ACCEPTED 2026-11-11 | `qrh-zeta23-density-v6-receipt.tar.gz` | `ca07a500aa8384b9…` |

Full hashes: [`receipts/SHA256SUMS`](receipts/SHA256SUMS). Each run re-judges everything in the
previous run of its line, so run 5 is the complete OpenAI-tree library and run 11 the complete
zeta23-tree layer. Each bundle holds the kit's `facts.tsv` or `receipt.json`, the axiom audit
`audit.out`, the report (`MNF_LIBRARY.md`, `MNF_ZETA23.md` or `MNF_DENSITY.md`) and the logs.

## Checked here, without a receipt

| what | how | evidence |
|---|---|---|
| [`core/`](core/) `MNFCore` | `lake build` (Lean 4.28.0) and a custom `#audit_all` over every `MNF.*` declaration: 307 entries, only the three standard axioms, no `sorryAx`, no `ofReduceBool`. Rebuilt from this repository's copy on 2026-11-23, audit output identical | [`core/audit.log`](core/audit.log) |
| [`extension/`](extension/) `MNF2` | Comparator pre-check at the OpenAI pin, Lean kernel + NanoDa, all 31 definitions compared, "Your solution is okay!", 2026-11-03. The same file, byte-identical (`25733057…`), is in the claim set of runs 7–11 | [`extension/comparator-precheck.log`](extension/comparator-precheck.log), [`extension/REPORT.md`](extension/REPORT.md) |

## That the files here are the judged files

- `rh/` and `zeta23/` are copies of add-ons v3 (`qrh-mnf-addon-v3`) and zeta23 v6
  (`qrh-zeta23-addon-v6`). `sha256sum -c MANIFEST.sha256` passes in each. The manifest hash is
  what the receipt records the run being launched with.
- The shared modules agree across lines. `MNF/RH/Core.lean`, `Gap.lean`, `Hypotheses.lean` and
  `Counting.lean` are byte-identical in `rh/` and `zeta23/`. `GapDensity.lean` differs in
  docstrings only (DEPOSIT_MAP §10).

## Errata

The deposit map's §10 lists nine errata found while the paper was prepared (warm versus cold
runs, definition counts as upper bounds, an omitted `@` block in the reports, and others). No
bundle was altered. Read them before quoting any receipt's prose.
