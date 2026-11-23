/-
  MNFCore.Conservation — the observable/confined budget of a pure two-qubit state
  and the dictionary between the three candidate "1/2" points, core-only.

  Experiment E2.  For the family |ψ(θ)⟩ = CRX(θ)(|−i⟩⊗|−i⟩) each qubit has
  Bloch length r = |cos(θ/2)| and the pair has concurrence C = |sin(θ/2)|, so

        r² + C² = 1                                   (quantum N + R = id)

  (the trigonometry lives in the Mathlib layer, MNFQ.Dictionary; here the budget
  identity is the hypothesis).  Three different quantities have been called "the
  1/2 point" in the corpus:

    (a) the coupling fraction α = θ/π            — Track B pre-registers a kink at α = 1/2;
    (b) the Bloch length r                        — the Bloch-sphere workbook puts Δ = 1/2 on r;
    (c) the observable share r² of the budget     — the equal split r² = C² = 1/2.

  This file proves the exact relations between (b) and (c) given only the budget
  identity, in particular that they are *different* points:

    equal_split_iff      : r = C  ⟺  r² = 1/2        (c) is the symmetric point
    r_half_gives         : r = 1/2  ⟹  C² = 3/4      (b) is not the symmetric point
    r2_half_not_r_half   : r² = 1/2  ⟹  r ≠ 1/2
    budget_as_N_R        : the shares (r², C²) are exactly (Nq, Rq) of a unit budget

  The link to (a), α = 1/2 ⟺ r² = 1/2 ⟺ θ = π/2, and r = 1/2 ⟺ α = 2/3, needs
  cos and is proved in MNFQ.Dictionary.  Whichever variable the hardware singles
  out (PREREG_E2, declaration D2), these theorems translate the result without
  ambiguity.
-/
import MNFCore.Operator

namespace MNF.Conservation

/-- Observable share and confined share of a pure two-qubit state. -/
structure Budget where
  r : Rat        -- Bloch length of either reduced state (0 ≤ r ≤ 1)
  C : Rat        -- concurrence (0 ≤ C ≤ 1)
  r_nonneg : 0 ≤ r
  C_nonneg : 0 ≤ C
  unit : r * r + C * C = 1

/-- The conservation law in share form: observable share + confined share = 1. -/
theorem shares_sum (b : Budget) : b.r * b.r + b.C * b.C = 1 := b.unit

/-- (c) The equal split r = C is exactly r² = 1/2. -/
theorem equal_split_iff (b : Budget) : b.r = b.C ↔ b.r * b.r = 1 / 2 := by
  have h := b.unit
  have hr := b.r_nonneg
  have hC := b.C_nonneg
  constructor
  · intro hrc; rw [← hrc] at h; grind
  · intro h2
    have hC2 : b.C * b.C = 1 / 2 := by grind
    -- both non-negative with equal squares ⟹ equal
    have : (b.r - b.C) * (b.r + b.C) = 0 := by grind
    rcases Rat.mul_eq_zero.mp this with h0 | h0
    · grind
    · -- r + C = 0 with r, C ≥ 0 forces r = C = 0, contradicting r² = 1/2
      have : b.r = 0 := by grind
      rw [this] at h2; grind

/-- (b) At r = 1/2 the confined share is 3/4: the state is mostly confined, not half. -/
theorem r_half_gives (b : Budget) (h : b.r = 1 / 2) : b.C * b.C = 3 / 4 := by
  have := b.unit; rw [h] at this; grind

/-- The two candidate thresholds (b) and (c) are different points. -/
theorem r2_half_not_r_half (b : Budget) (h : b.r * b.r = 1 / 2) : b.r ≠ 1 / 2 := by
  intro h'; rw [h'] at h; grind

/-- At r = 1/2, C² = 3/4 > r²: the confined share dominates. -/
theorem r_half_confined_dominates (b : Budget) (h : b.r = 1 / 2) : b.r * b.r < b.C * b.C := by
  have := r_half_gives b h; rw [h, this]; grind

/-- The shares are literally N and R of a unit budget at threshold Δ = r²:
    Nq Δ 1 keeps the whole budget observable iff Δ ≤ 1 — true — so the
    bookkeeping N + R = id applied to the unit budget with "observable part r²
    and remainder C²" is the identity r² + C² = 1 (unit). -/
theorem budget_as_N_R (b : Budget) :
    MNF.Nq (b.r * b.r) (b.r * b.r) + (1 - b.r * b.r) = 1 ∧ 1 - b.r * b.r = b.C * b.C := by
  constructor
  · rw [MNF.Nq_at_threshold]; grind
  · have := b.unit; grind

/-- Classification of the observable share at Δ = 1/2 across the family:
    r² > 1/2 ⟹ observable; 0 < r² < 1/2 ⟹ reservoir; r = 0 ⟹ zero. -/
theorem class_of_share_observable (b : Budget) (h : 1 / 2 ≤ b.r * b.r) :
    MNF.classifyQ (1 / 2) (b.r * b.r) = .observable := by
  apply MNF.classifyQ_observable
  · grind
  · exact h

theorem class_of_share_reservoir (b : Budget) (h0 : 0 < b.r) (h : b.r * b.r < 1 / 2) :
    MNF.classifyQ (1 / 2) (b.r * b.r) = .reservoir := by
  apply MNF.classifyQ_reservoir
  · have := Rat.mul_pos h0 h0; grind
  · exact h

/-- Concrete instances of the family (exact values of r² at α = 1/3, 1/2, 2/3):
    cos²(π/6) = 3/4, cos²(π/4) = 1/2, cos²(π/3) = 1/4 (trigonometry in MNFQ). -/
def budget_of_r2 (r2 : Rat) (r C : Rat)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hr2 : r * r = r2) (hC2 : C * C = 1 - r2) : Budget :=
  ⟨r, C, hr, hC, by rw [hr2, hC2]; grind⟩

end MNF.Conservation
