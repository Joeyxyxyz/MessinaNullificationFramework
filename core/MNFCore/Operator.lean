/-
  MNFCore.Operator — the Messina nullification operator, core-only.

  Messina Nullification Framework (MNF) · quantum-experiment package v0.1
  Lean 4.28.0, no Mathlib, no `native_decide`, no axioms beyond the kernel's.

  N(Δ,x) keeps x when it reaches the threshold Δ and nullifies it otherwise;
  R(Δ,x) is the remainder, so N + R = id (the conservation law).  The three
  classes are [0] (x = 0), [0.0e] (0 < x < Δ, the reservoir) and [1] (Δ ≤ x,
  observable).  Definitions follow Batch 1 of the corpus (classification &
  remainder); this file re-proves them without `native_decide` and adds the
  dilation-covariance statements the experiments rely on.

  Every theorem is checked by the kernel: see AXIOM_AUDIT.md for `#print axioms`.
-/

namespace MNF

/-- Threshold (nullification) operator on ℕ. -/
def N (Δ x : Nat) : Nat := if Δ ≤ x then x else 0

/-- Remainder operator on ℕ. -/
def R (Δ x : Nat) : Nat := if Δ ≤ x then 0 else x

/-- The three MNF classes. -/
inductive NullClass where
  | zero        -- [0]   true vacuum
  | reservoir   -- [0.0e] exists, below threshold
  | observable  -- [1]   at or above threshold
  deriving DecidableEq, Repr

/-- Classification of x against Δ. -/
def classify (Δ x : Nat) : NullClass :=
  if x = 0 then .zero else if Δ ≤ x then .observable else .reservoir

/-! ### Conservation and idempotence -/

/-- N + R = id (the conservation law of the framework). -/
theorem conservation (Δ x : Nat) : N Δ x + R Δ x = x := by
  unfold N R; split <;> omega

theorem N_idem (Δ x : Nat) : N Δ (N Δ x) = N Δ x := by
  unfold N; split <;> simp_all

theorem R_idem (Δ x : Nat) : R Δ (R Δ x) = R Δ x := by
  unfold R; split <;> simp_all

/-- Nullifying the remainder gives nothing: the reservoir is invisible to N. -/
theorem N_R (Δ x : Nat) : N Δ (R Δ x) = 0 := by
  unfold N R; split <;> simp_all

/-- The observable part leaves no remainder. -/
theorem R_N (Δ x : Nat) : R Δ (N Δ x) = 0 := by
  unfold N R; split <;> simp_all

theorem N_zero (Δ : Nat) : N Δ 0 = 0 := by unfold N; split <;> rfl
theorem R_zero (Δ : Nat) : R Δ 0 = 0 := by unfold R; split <;> rfl

/-- Exactly at the threshold the value is observable and nothing is left over. -/
theorem N_at_threshold (Δ : Nat) : N Δ Δ = Δ := by unfold N; simp
theorem R_at_threshold (Δ : Nat) : R Δ Δ = 0 := by unfold R; simp

/-! ### The classes are exhaustive and disjoint -/

theorem classify_zero (Δ : Nat) : classify Δ 0 = .zero := by unfold classify; simp

theorem classify_observable (Δ x : Nat) (hx : x ≠ 0) (h : Δ ≤ x) :
    classify Δ x = .observable := by
  unfold classify; simp [hx, h]

theorem classify_reservoir (Δ x : Nat) (hx : x ≠ 0) (h : x < Δ) :
    classify Δ x = .reservoir := by
  unfold classify; simp [hx, Nat.not_le.mpr h]

theorem classify_eq_observable_iff (Δ x : Nat) :
    classify Δ x = .observable ↔ (x ≠ 0 ∧ Δ ≤ x) := by
  unfold classify
  by_cases hx : x = 0
  · simp [hx]
  · by_cases h : Δ ≤ x <;> simp [hx, h]

theorem classify_eq_reservoir_iff (Δ x : Nat) :
    classify Δ x = .reservoir ↔ (x ≠ 0 ∧ x < Δ) := by
  unfold classify
  by_cases hx : x = 0
  · simp [hx]
  · by_cases h : Δ ≤ x <;> simp [hx, h] <;> omega

theorem classify_eq_zero_iff (Δ x : Nat) : classify Δ x = .zero ↔ x = 0 := by
  unfold classify
  by_cases hx : x = 0
  · simp [hx]
  · by_cases h : Δ ≤ x <;> simp [hx, h]

/-- Reservoir values are exactly those with full remainder and no observable part. -/
theorem reservoir_iff (Δ x : Nat) :
    classify Δ x = .reservoir ↔ (x ≠ 0 ∧ N Δ x = 0 ∧ R Δ x = x) := by
  rw [classify_eq_reservoir_iff]; unfold N R
  constructor
  · rintro ⟨hx, h⟩; simp [Nat.not_le.mpr h, hx]
  · rintro ⟨hx, hN, hR⟩
    refine ⟨hx, ?_⟩
    by_cases h : Δ ≤ x
    · simp [h] at hN; exact absurd hN hx
    · exact Nat.lt_of_not_le h

/-! ### Dilation covariance
  N(λΔ, λx) = λ·N(Δ, x) for λ > 0: the operator carries no scale of its own.
  Only the dimensionless ratio x/Δ enters the classification. -/

theorem dilation_N (lam Δ x : Nat) (hl : 0 < lam) :
    N (lam * Δ) (lam * x) = lam * N Δ x := by
  unfold N
  have : lam * Δ ≤ lam * x ↔ Δ ≤ x := by
    constructor
    · exact fun h => Nat.le_of_mul_le_mul_left h hl
    · exact fun h => Nat.mul_le_mul_left lam h
  by_cases h : Δ ≤ x
  · simp [h, this]
  · simp [h, this]

theorem dilation_R (lam Δ x : Nat) (hl : 0 < lam) :
    R (lam * Δ) (lam * x) = lam * R Δ x := by
  unfold R
  have : lam * Δ ≤ lam * x ↔ Δ ≤ x := by
    constructor
    · exact fun h => Nat.le_of_mul_le_mul_left h hl
    · exact fun h => Nat.mul_le_mul_left lam h
  by_cases h : Δ ≤ x
  · simp [h, this]
  · simp [h, this]

/-- The classification is scale-free. -/
theorem dilation_classify (lam Δ x : Nat) (hl : 0 < lam) :
    classify (lam * Δ) (lam * x) = classify Δ x := by
  unfold classify
  have hle : lam * Δ ≤ lam * x ↔ Δ ≤ x := by
    constructor
    · exact fun h => Nat.le_of_mul_le_mul_left h hl
    · exact fun h => Nat.mul_le_mul_left lam h
  have hz : lam * x = 0 ↔ x = 0 := by
    constructor
    · intro h; rcases Nat.mul_eq_zero.mp h with h | h
      · omega
      · exact h
    · intro h; simp [h]
  by_cases hx : x = 0
  · simp [hx]
  · by_cases h : Δ ≤ x
    · simp [hx, h, hle, hz]
    · simp [hx, h, hle, hz]

/-! ### ℚ-valued version (Bloch-length variable lives in [0,1] ⊂ ℚ ⊂ ℝ) -/

/-- Threshold operator on ℚ. -/
def Nq (Δ x : Rat) : Rat := if Δ ≤ x then x else 0
/-- Remainder on ℚ. -/
def Rq (Δ x : Rat) : Rat := if Δ ≤ x then 0 else x

/-- Classification of a non-negative rational against Δ. -/
def classifyQ (Δ x : Rat) : NullClass :=
  if x = 0 then .zero else if Δ ≤ x then .observable else .reservoir

theorem conservation_q (Δ x : Rat) : Nq Δ x + Rq Δ x = x := by
  unfold Nq Rq; split <;> grind

theorem Nq_at_threshold (Δ : Rat) : Nq Δ Δ = Δ := by unfold Nq; simp [Rat.le_refl]
theorem Rq_at_threshold (Δ : Rat) : Rq Δ Δ = 0 := by unfold Rq; simp [Rat.le_refl]

theorem Nq_idem (Δ x : Rat) : Nq Δ (Nq Δ x) = Nq Δ x := by
  unfold Nq; split <;> simp_all

theorem classifyQ_observable (Δ x : Rat) (hx : x ≠ 0) (h : Δ ≤ x) :
    classifyQ Δ x = .observable := by
  unfold classifyQ; simp [hx, h]

theorem classifyQ_reservoir (Δ x : Rat) (hx : x ≠ 0) (h : x < Δ) :
    classifyQ Δ x = .reservoir := by
  unfold classifyQ; simp [hx, Rat.not_le.mpr h]

theorem classifyQ_zero (Δ : Rat) : classifyQ Δ 0 = .zero := by unfold classifyQ; simp

/-- Dilation covariance over ℚ: scaling x and Δ by the same λ > 0 changes nothing. -/
theorem dilation_Nq (lam Δ x : Rat) (hl : 0 < lam) :
    Nq (lam * Δ) (lam * x) = lam * Nq Δ x := by
  unfold Nq
  have hiff : lam * Δ ≤ lam * x ↔ Δ ≤ x := by
    constructor
    · exact fun h => Rat.le_of_mul_le_mul_left h hl
    · exact fun h => Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hl)
  by_cases h : Δ ≤ x
  · simp [h, hiff]
  · simp [h, hiff]

theorem dilation_classifyQ (lam Δ x : Rat) (hl : 0 < lam) :
    classifyQ (lam * Δ) (lam * x) = classifyQ Δ x := by
  unfold classifyQ
  have hiff : lam * Δ ≤ lam * x ↔ Δ ≤ x := by
    constructor
    · exact fun h => Rat.le_of_mul_le_mul_left h hl
    · exact fun h => Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hl)
  have hz : lam * x = 0 ↔ x = 0 := by
    constructor
    · intro h
      rcases Rat.mul_eq_zero.mp h with h | h
      · exact absurd h (Rat.ne_of_gt hl)
      · exact h
    · intro h; simp [h]
  by_cases hx : x = 0
  · simp [hx]
  · by_cases h : Δ ≤ x
    · simp [hx, h, hiff, hz]
    · simp [hx, h, hiff, hz]

end MNF
