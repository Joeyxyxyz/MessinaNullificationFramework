/-
  NULLIFICATION BATCH 1: Classification & Remainder
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
-- CLASSIFICATION THEOREMS
-- ============================================================================

/--
PROVIDED SOLUTION: The classify function returns one of three values by definition.
Use cases or decide tactic.
-/
theorem classification_exhaustive (Δ : Nat) (x : Nat) :
    (classify Δ x = NullClass.zero ∨ 
     classify Δ x = NullClass.observable ∨ 
     classify Δ x = NullClass.nullified) := by
  sorry

/--
PROVIDED SOLUTION: If classify returns zero, it can't return observable or nullified.
Intro h, constructor, both follow from h by congruence.
-/
theorem classification_unique_zero (Δ : Nat) (x : Nat) :
    classify Δ x = NullClass.zero → 
    (classify Δ x ≠ NullClass.observable ∧ classify Δ x ≠ NullClass.nullified) := by
  sorry

/--
PROVIDED SOLUTION: Same pattern as above.
-/
theorem classification_unique_observable (Δ : Nat) (x : Nat) :
    classify Δ x = NullClass.observable → 
    (classify Δ x ≠ NullClass.zero ∧ classify Δ x ≠ NullClass.nullified) := by
  sorry

/--
PROVIDED SOLUTION: Same pattern.
-/
theorem classification_unique_nullified (Δ : Nat) (x : Nat) :
    classify Δ x = NullClass.nullified → 
    (classify Δ x ≠ NullClass.zero ∧ classify Δ x ≠ NullClass.observable) := by
  sorry

-- ============================================================================
-- REMAINDER THEOREMS
-- ============================================================================

/--
PROVIDED SOLUTION: Unfold classify and R. If nullified, then x ≠ 0 and x < Δ.
So R returns x. Use simp and split.
-/
theorem remainder_when_nullified (Δ : Nat) (x : Nat) :
    classify Δ x = NullClass.nullified → R Δ x = x := by
  sorry

/--
PROVIDED SOLUTION: Unfold classify and R. If observable, then x >= Δ.
So R returns 0. Use simp and omega.
-/
theorem remainder_when_observable (Δ : Nat) (x : Nat) :
    classify Δ x = NullClass.observable → R Δ x = 0 := by
  sorry

/--
PROVIDED SOLUTION: Unfold R, split on x >= Δ. If true, R = 0. If false, R = x < Δ.
Either way, R < Δ or R = 0.
-/
theorem remainder_bound (Δ : Nat) (x : Nat) (hΔ : Δ > 0) :
    R Δ x < Δ ∨ R Δ x = 0 := by
  sorry

/--
PROVIDED SOLUTION: Unfold R. 0 < Δ so returns 0.
-/
theorem R_zero (Δ : Nat) : R Δ 0 = 0 := by
  sorry

/--
PROVIDED SOLUTION: Unfold N and R. Split on x >= Δ. Both cases: x + 0 = x or 0 + x = x.
-/
theorem conservation (Δ : Nat) (x : Nat) : N Δ x + R Δ x = x := by
  sorry

/--
PROVIDED SOLUTION: Unfold R. Δ >= Δ is true, so returns 0.
-/
theorem R_at_threshold (Δ : Nat) : R Δ Δ = 0 := by
  sorry

#check @classification_exhaustive
#check @classification_unique_zero
#check @classification_unique_observable
#check @classification_unique_nullified
#check @remainder_when_nullified
#check @remainder_when_observable
#check @remainder_bound
#check @R_zero
#check @conservation
#check @R_at_threshold
