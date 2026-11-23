/-
  NULLIFICATION BATCH 2: Monotonicity, Boundary, Composition
  10 theorems for Aristotle
-/

def N (Δ : Nat) (x : Nat) : Nat := 
  if x >= Δ then x else 0

def R (Δ : Nat) (x : Nat) : Nat := 
  if x >= Δ then 0 else x

inductive NullClass where
  | zero        
  | observable  
  | nullified   
  deriving DecidableEq, Repr

def classify (Δ : Nat) (x : Nat) : NullClass :=
  if x = 0 then NullClass.zero
  else if x >= Δ then NullClass.observable
  else NullClass.nullified

-- ============================================================================
-- MONOTONICITY
-- ============================================================================

/--
PROVIDED SOLUTION: Unfold N. Case split on x >= Δ and y >= Δ.
Four cases, all resolve with omega using h : x ≤ y.
-/
theorem N_monotone (Δ : Nat) (x y : Nat) (h : x ≤ y) :
    N Δ x ≤ N Δ y := by
  sorry

/--
PROVIDED SOLUTION: Unfold N. If x >= Δ₂ then x >= Δ₁ (since Δ₁ ≤ Δ₂), both return x.
If x < Δ₂ but x >= Δ₁, then N_Δ₂ = 0, N_Δ₁ = x, so 0 ≤ x.
If x < Δ₁ then both return 0.
-/
theorem threshold_monotone (Δ₁ Δ₂ : Nat) (x : Nat) (h : Δ₁ ≤ Δ₂) :
    N Δ₂ x ≤ N Δ₁ x := by
  sorry

-- ============================================================================
-- BOUNDARY BEHAVIOR
-- ============================================================================

/--
PROVIDED SOLUTION: Unfold N. Δ >= Δ is true, so returns Δ.
-/
theorem at_threshold (Δ : Nat) (hΔ : Δ > 0) : N Δ Δ = Δ := by
  sorry

/--
PROVIDED SOLUTION: Unfold N. Δ - 1 < Δ (since Δ > 0), so returns 0.
-/
theorem just_below_threshold (Δ : Nat) (hΔ : Δ > 0) : N Δ (Δ - 1) = 0 := by
  sorry

/--
PROVIDED SOLUTION: Unfold classify. Δ > 0 so Δ ≠ 0. Δ >= Δ, so returns observable.
-/
theorem at_threshold_observable (Δ : Nat) (hΔ : Δ > 0) :
    classify Δ Δ = NullClass.observable := by
  sorry

/--
PROVIDED SOLUTION: Unfold classify. Δ - 1 could be 0 if Δ = 1. 
Split cases. If Δ = 1, then Δ - 1 = 0, returns zero.
If Δ > 1, then Δ - 1 ≠ 0 and Δ - 1 < Δ, returns nullified.
-/
theorem below_threshold_class (Δ : Nat) (hΔ : Δ > 1) :
    classify Δ (Δ - 1) = NullClass.nullified := by
  sorry

-- ============================================================================
-- COMPOSITION
-- ============================================================================

/--
PROVIDED SOLUTION: Unfold N twice. If x >= Δ, then N x = x >= Δ, so N(N x) = x.
If x < Δ, then N x = 0 < Δ, so N(N x) = 0. Either way N(N x) = N x.
-/
theorem idempotent (Δ : Nat) (x : Nat) : N Δ (N Δ x) = N Δ x := by
  sorry

/--
PROVIDED SOLUTION: By spectral_gap, N x = 0 or N x >= Δ.
If N x = 0, then R(N x) = R(0) = 0.
If N x >= Δ, then R(N x) = 0 by definition.
-/
theorem R_comp_N (Δ : Nat) (x : Nat) : R Δ (N Δ x) = 0 := by
  sorry

/--
PROVIDED SOLUTION: R x < Δ or R x = 0 (by remainder_bound-like reasoning).
If R x = 0, N(0) = 0.
If R x < Δ, N(R x) = 0.
-/
theorem N_comp_R (Δ : Nat) (x : Nat) : N Δ (R Δ x) = 0 := by
  sorry

/--
PROVIDED SOLUTION: Unfold N. Split on x >= Δ. 
Right case: x >= Δ so N x = x, done apply Or.inr.
Left case: x < Δ so N x = 0, done apply Or.inl.
-/
theorem spectral_gap (Δ : Nat) (x : Nat) : N Δ x = 0 ∨ N Δ x >= Δ := by
  sorry

#check @N_monotone
#check @threshold_monotone
#check @at_threshold
#check @just_below_threshold
#check @at_threshold_observable
#check @below_threshold_class
#check @idempotent
#check @R_comp_N
#check @N_comp_R
#check @spectral_gap
