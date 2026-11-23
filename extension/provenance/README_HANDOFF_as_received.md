# MNF beyond projection — handoff package for the Lean session (Ubuntu)

Prepared 2026-11-03 on the Windows laptop (QuantumMphirst) by the Claude Code session that ran Joey's BlueQubit OTOC hackathon
(Oct 24–25, 2026) and then, at Joey's request, explored the Messina Nullification Framework (MNF) beyond its projection operator:
injection, ejection, cascades, residues, and the literature placement of each. Nothing in this package was machine-checked:
the Windows laptop has no Lean toolchain. **That is the job of the Ubuntu session.**

## What is in the package

| path | what | status |
|---|---|---|
| `MNF_beyond_projection.md` | the synthesis document: the corpus algebra as it stands, the proposed extension (injection = fragmentation of a representation, ejection = the retraction `E(Δ,x) = sgn(x)·max(|x|,Δ)`, the deficit `J = E − id`, cascades over threshold ladders, the signed cancellation residue), what the hackathon data demonstrated, the literature table, open questions | written by the synthesis agent, checked by an adversarial agent (see `verify/`) |
| `MNF_Injection_Ejection.lean` | **the Lean sketch to compile**: proposed definitions and theorem statements for `E`, `J`, `I_k` (fragmentation), `nu` (piecewise reading), `delta_star`, `residue`, with proof attempts where the proof is short | **UNVERIFIED — never compiled** |
| `formal/catalogue.md` | every operation in the 301-file corpus beyond the plain projector, with the quoted Lean definition, every theorem about it and its proof status read from the source (proved / sorry / axiom / True-stub / exact? / negated), the ~100 re-declarations of N across six carrier types, and the inconsistencies between files | read, not compiled |
| `algebra/algebra.md`, `algebra/mnf_ops.py`, `algebra/worked_examples.py` | the operator-algebra design and a numpy implementation with randomized property self-tests (`python -I mnf_ops.py`) | self-tests pass; proofs are prose, unverified |
| `lab/results.md` (+ scripts, json, png) | the OTOC hackathon data treated as real cascades: ejection events, injection by fragmentation (13/13 distinct variant pairs on G3; 23 draws counting identical repeats), δ* vs expansion size (Spearman −0.54 / −0.52), probe readings, type-A degenerate zeros on the real S3 circuit with exact truth, the Bloch-length probe across χ | measured; every number carries its n |
| `lit/placement.md` | each MNF operation's standard name and closest reference, and what MNF adds | literature, cited |
| `verify/` | the adversarial check's notes: recomputed numbers, counterexamples found, corrections | |
| `corpus_pointers.md` | where the corpus lives and which files the sketch builds on | |

## Pinned environment (from the corpus file headers and the project lakefiles on the Windows side)

```
leanprover/lean4:v4.24.0
Mathlib commit f897ebcf72cd16f89ab4577d0c826cd14afaafc7   (messina_AFM_submission_package/lakefile.lean)
```
`comparator_run/` and `nullification_project/` use the same toolchain (`nullification_project` requires Mathlib `@ "v4.24.0"`).
The sketch imports `Mathlib` and uses only `Real`, `abs`, `max`, `Finset.sum` and order lemmas; it should elaborate in any of those projects.

## What to do in the Ubuntu session

1. Drop `MNF_Injection_Ejection.lean` into the project that already builds (the one that handled the Batch/Aristotle files) and run
   `lake env lean MNF_Injection_Ejection.lean`. Record every error. Fix type errors; where a proof fails, replace it by `sorry` and
   keep the statement — the statements are the deliverable, the proofs are a first attempt.
2. Report back three lists: (a) definitions that elaborate, (b) theorems proved, (c) theorems left as `sorry` with the goal state at
   the failure. Keep the file's docstrings: each one says whether the item is [CORPUS] (already in Joey's corpus) or [PROPOSED].
3. Optional but valuable: run the same `lake env lean` over the corpus files the sketch cites (`Nullification_Core.lean`,
   `Batch4_2_DegenerateZeroMechanisms-1.lean`, `MNFmeetsDavisSet4.lean`, `Batch17_ToroidNullification.lean`,
   `output56_signed_nullification.lean`, `Batch12_PartitionPower_Aristotle_aristotle.lean`, `Nullification_Aristotle_Extension.lean`) and
   confirm or correct the proof-status column in `formal/catalogue.md` §5 — it was produced by reading, and a compiler is the authority.
4. Do NOT change the corpus files themselves; put results in a new file or a report.

## The three honesty tags used everywhere in this package

* **(a) corpus** — defined or proved in Joey's Lean corpus (status as read; see 3 above).
* **(b) proposed** — designed in this exploration; prose proofs or Lean statements, unverified.
* **(c) data** — observed on the hackathon files (G2/G3/G4 pauli-path and MPS runs; S2/S3/G1 exact truth; the real S3 circuit).
No sorry'd theorem is presented as proved; where the catalogue says "proved" it means "a complete proof text is present".

## One-paragraph context for whoever reads this cold

MNF's core is the hard-threshold operator N(Δ,x) = x if |x| ≥ Δ else 0, the remainder R = x − N, the identity N + R = id, three
classes ([0] true zero, [0.0e] confined reservoir 0 < |x| < Δ, [1] observable), idempotence, monotonicity, dilation covariance and
non-distributivity (pool accumulation). The corpus defines *ejection* only as the predicate x = Δ (the reservoir crossing to [1], probe
reading Δ/2) and never defines *injection*. The exploration proposes: injection is fragmentation of a representation (split one
observable value into k sub-threshold pieces; the value is unchanged, the piecewise reading goes to 0; identity ν_Δ∘I_k = N_{kΔ}:
injection is threshold dilation); ejection is the retraction E(Δ,x) = sgn(x)·max(|x|,Δ), the "ceiling" into the gapped set, dual to N
as the "floor" (E ⊣ incl ⊣ N on the half-line); the two are not inverse but live on different levels (content vs representation).
On real data (BlueQubit pauli-path, where the platform's transpiler lands the same circuit on different representations), fragmentation
is what the `max_paulis` count measured: the fragmented representation reads 0 or a sign-flipped residue where the compact one reads the
value (13/13 distinct same-threshold variant pairs on G3, one-sided p 1.2e-4), and selecting the compact representation, never averaging in the fragmented ones, took G3
from 373 to 430/800 and, with a sign-consistency gate (contradicted signs = cancellation residue → 0), G4 from 48 to 118 and then to
298 with an expansion-size magnitude cue.
