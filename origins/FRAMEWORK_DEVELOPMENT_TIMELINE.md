# Framework Development Timeline
## From Zenodo 15763702 to Comparator-checked Lean

### July 2025 — Origin
**Zenodo 15763702**  
Universal Gauge Theory Mass Gaps: The Messina Nullification Framework…  
Introduces \(N = \prod_j P_j\), reports >200 IBM runs (U(1)–SU(10), 3–127 qubits), SU(3) gaps 1.84–2.3 GeV, SU(4) AdS/CFT 1.8413 GeV.

### October 2025
**Zenodo 17370031**  
Gluonic Isolation via the Nullification Operator…  
Formalizes \(N = I - P\) (or product of projectors), idempotency/hermiticity/gauge covariance, IBM Brisbane results up to 126 qubits (gap 1.92 GeV / 5.282 lattice units).

### December 2025
**Zenodo 18077944**  
The Nullification Operator: Algebraic Core…  
Conservation \(N(x) + R(x) = x\), three-valued classification, NSA correspondence, multi-AI audit, reproducibility code.

### March 2026
**Zenodo 18902403**  
Messina Nullification Framework v3, Volume 1: Core Operator Library  
Full algebraic foundation \(N(\Delta, x)\), Aristotle-verified Lean (140 theorems, zero sorry), spectral-gap → mass-gap lower bound, gauge invariance, Wightman compatibility. Volumes 2 (RH) and 3 (physical) accompany it.

### Late 2026 — Lean / Comparator layer
- **Joeyxyxyz/qrh-comparator-receipts**  
  MNF.RH library (Core, Gap, Hypotheses, Unconditional, Counting, Reduction, Schrödinger, GapDensity) Comparator-accepted on OpenAI’s 7/8 zero-free region tree (v1–v3) and on Anthropic’s zeta23 tree (including density extensions up to 480 theorems).  
  Receipts show only the three permitted axioms.

- **Joeyxyxyz/sturm-liouville-comparator-run**  
  Lean formalization of Sturm–Liouville eigenvalue simplicity for confining potentials. Comparator-accepted (Lean kernel + NanoDa). Used in the MNF.RH Schrödinger-bridge arguments.

### Relation to the pure-Yang package
The generator, pre-registration v1.1, and comparison note are the circuit-side continuation of this line: they keep the nullification that began in 15763702, use the structural Wilson terms isolated by later formalizations, and sit next to the OpenAI continuum existence statement while the Lean/Comparator work supplies the precise gap-after-nullify equivalences.

All of the above is now the active development trunk.
