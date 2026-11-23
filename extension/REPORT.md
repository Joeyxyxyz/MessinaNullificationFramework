# MNF beyond projection — compile report for the handoff of 2026-11-03

Joey Messina's Ubuntu laptop, 2026-11-03, Claude Code. Answers steps 1–3 of `README_HANDOFF_as_received.md`.

## Result in one line

`MNF_Injection_Ejection.lean` is fully proved: 31 definitions elaborate, 56/56 theorems close
with no `sorry`, every theorem depends on exactly `[propext, Classical.choice, Quot.sound]`, and
Comparator accepted all 56 against a sorry'd mirror challenge with every definition compared by
name, type and body, under the Lean kernel and NanoDa.

## Environment

| | handoff said | used here |
|---|---|---|
| Lean | v4.24.0 | **v4.34.1** |
| Mathlib | `f897ebcf` | **`d13f23b723b8a846827a245b89c10fc7d3f11612`** |

The file was checked only at the newer pin (the tree already built for the MNF.RH add-ons).
Nothing in it is pin-sensitive beyond lemma names, and the proofs that came with the sketch
closed unchanged, so a port back to v4.24.0 is expected to be mechanical, but it was not done.

## (a) Definitions that elaborate: all 31

`nullify remainder NorthProbe SouthProbe IsEjectionThreshold IsReservoir Gapped eject deficit
metricProj Rep content nu hidden eps SameSign inject compact refine kstar cascade deltaStar
inProcessStep inProcess postHoc residue signGate softGate softNullify injectAdd ejectAdd`.
(`open scoped Classical` in the sketch already answered the adversarial check's A1.)

## (b) Theorems proved: all 56

As received, the sketch compiled with **zero errors** (`compile-sketch-as-received.log`): its
18 attempted proofs all closed as written (`conservation idempotent' dilation_covariance
abs_nullify_antitone_in_threshold eject_probe_reading nullify_floor northProbe_deficit
eject_eq_id_add_deficit nullify_eq_id_sub_deficit_sq rep_conservation content_inject
inject_nullified compact_inject nullify_sees_through ladder_not_composite residue_eq
hardGate_is_nullify injectAdd_ejectAdd`), and 38 were `sorry`.

The 38 were then proved here, statements untouched, in eight parallel batches, each batch
compiling its own copy until clean (`compile-proved.log` is the assembled file's check):

`eject_gapped eject_idem nullify_eject eject_nullify remainder_eject eject_sub_nullify
eject_dilation nullify_comp_nullify eject_comp_eject eject_ceiling deficit_deficit
deficit_tripotent nullify_deficit metricProj_branch metricProj_deficit_swap
rep_not_distributive nu_inject eps_inject inject_at_kstar eventual_nullification
typeA_on_demand refine_inject deltaStar_singleton nu_eq_zero_of_all_below deltaStar_inject
sameSign_refine_le sameSign_nu_le_content sameSign_sign mixed_refine_can_increase
zero_reading_uninformative inProcess_ne_postHoc two_piece_sign_safe residue_both_signs
realise gate_minimax soft_idem_iff soft_no_gap ejectAdd_not_additive`

Thirteen helper lemmas were added, each immediately before the theorem it serves and named
`aux_<theorem>_<n>` (e.g. `aux_eject_idem_1`: `Gapped Δ y → eject Δ y = y`;
`aux_deficit_deficit_1`: the closed form of `deficit`). They are proved, audited, and present
in the challenge mirror, but are not listed in `config.json` (they are not claims).

## (c) Theorems left as `sorry`: none

No statement had to be changed or weakened. No statement was found false.

## Checks (all files in this folder)

- `audit.out`: 56 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `comparator-precheck.log`: Comparator v4.34.0 `d03acab1` (lean4export `076e8e57`, landrun
  `811cfff5`, NanoDa `68d5ca9d`), challenge `Challenge.lean` (= the module with every proof
  `sorry`, 69 sorries), solution `MNF2.InjectionEjection`, `definition_names = []` so every
  definition reached by a statement was compared by body: `nanoda kernel accepts the solution`,
  `Lean default kernel accepts the solution`, `Your solution is okay!`, exit 0. Warm run on the
  author's account, outside the QRH launcher; the Lake project is `~/mnf-stageA/lib-mnf2`
  (`lakefile.toml`, `lean-toolchain` copied here).

## Step 3 of the handoff (compile the cited corpus files): not done

The corpus files the sketch cites (`Nullification_Core.lean`, `Batch4_2_…`, `MNFmeetsDavisSet4.lean`,
`Batch17_…`, `output56_…`, `Batch12_…`, `Nullification_Aristotle_Extension.lean`) are not on this
machine or on the drive; the handoff's paths are Windows-side. When Joey copies the 301-file
corpus to the drive, the same `lake env lean` pass settles the proof-status column of
`formal/catalogue.md` §5. Known from that catalogue already: eight files are mojibake on disk
and Batch4_1/4_2 contain `decide` proofs of false instances, so a clean subset is the target.

## Notes for the package's authors

- The adversarial check's A1 (missing `Decidable (IsReservoir Δ x)`) was already fixed in the
  file by `open scoped Classical`; its "fragile" proofs (`content_inject`, `dilation_covariance`,
  `hardGate_is_nullify`) all closed as written at this pin.
- Unused hypotheses: `soft_no_gap` does not use `hg1 : g < 1` (the adversarial check's B3 stands:
  the theorem is weaker than the prose claim); two `hΔ` binders are unused (compile warnings at
  the sketch's lines 151 and 291). Statements were left as received.
- `if_pos`/`if_neg` are deprecated at this Mathlib; the proofs that use them still compile.
- The header's inventory of Mathlib notions used was wrong (adversarial check B6) and has been
  corrected in `MNF_Injection_Ejection.lean`'s header, together with the STATUS paragraph.

## Where this sits in the register

This file is about the threshold operator N and its algebra on ℝ and on finite lists of reals.
It proves nothing about ζ, says nothing about RH, and does not touch `SpectralGapHyp` or any
MNF.RH theorem. In the deposit map's categories it is **proved (kernel-checked), operator algebra**:
useful as the formal backbone of the OTOC/cascade reading, not as progress on the zeta problem.
It has not been added to any receipt bundle or to DEPOSIT_MAP.md; both are unchanged.
