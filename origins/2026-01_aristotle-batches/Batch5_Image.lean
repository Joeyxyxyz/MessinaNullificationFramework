/-
  NULLIFICATION BATCH 5: Image & Projection Properties
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
-- IMAGE CHARACTERIZATION
-- ============================================================================

/--
PROVIDED SOLUTION: 
(→) If ∃ y, N y = x, then by spectral_gap, N y = 0 or N y >= Δ. So x = 0 or x >= Δ.
(←) If x = 0, take y = 0, N 0 = 0 = x. If x >= Δ, take y = x, N x = x.
-/
theorem in_image_N (Δ : Nat) (x : Nat) :
    (∃ y, N Δ y = x) ↔ (x = 0 ∨ x >= Δ) := by
  sorry

/--
PROVIDED SOLUTION: Take y = 0. N Δ 0 = 0.
-/
theorem zero_in_image (Δ : Nat) : ∃ y, N Δ y = 0 := by
  sorry

/--
PROVIDED SOLUTION: x >= Δ, so N x = x. Take y = x.
-/
theorem observable_in_image (Δ : Nat) (x : Nat) (h : x >= Δ) : ∃ y, N Δ y = x := by
  sorry

/--
PROVIDED SOLUTION: Suppose ∃ y, N y = x with 0 < x < Δ.
By spectral_gap, N y = 0 or N y >= Δ. 
If N y = 0 then x = 0, contradiction.
If N y >= Δ then x >= Δ, contradiction.
-/
theorem gap_not_in_image (Δ : Nat) (x : Nat) (h1 : 0 < x) (h2 : x < Δ) :
    ¬∃ y, N Δ y = x := by
  sorry

-- ============================================================================
-- PROJECTION PROPERTIES
-- ============================================================================

/--
PROVIDED SOLUTION: Unfold N twice. Case split. Already proven as idempotent.
-/
theorem N_idempotent (Δ : Nat) (x : Nat) : N Δ (N Δ x) = N Δ x := by
  sorry

/--
PROVIDED SOLUTION: Generalize idempotent to all x.
-/
theorem N_projection (Δ : Nat) : ∀ x, N Δ (N Δ x) = N Δ x := by
  sorry

/--
PROVIDED SOLUTION: N(N(N x)) = N(N x) by idempotent. N(N x) = N x by idempotent.
-/
theorem N_triple (Δ : Nat) (x : Nat) : N Δ (N Δ (N Δ x)) = N Δ x := by
  sorry

/--
PROVIDED SOLUTION: If x is in image of N, then N x = x.
By in_image_N, x = 0 or x >= Δ.
If x = 0, N 0 = 0 = x.
If x >= Δ, N x = x.
-/
theorem fixed_point_iff (Δ : Nat) (x : Nat) :
    N Δ x = x ↔ (x = 0 ∨ x >= Δ) := by
  sorry

-- ============================================================================
-- RANGE PROPERTIES
-- ============================================================================

/--
PROVIDED SOLUTION: By spectral_gap, N x = 0 or N x >= Δ.
-/
theorem N_range (Δ : Nat) (x : Nat) : N Δ x = 0 ∨ N Δ x >= Δ := by
  sorry

/--
PROVIDED SOLUTION: The gap (0, Δ) is empty. Negation of (N x > 0 ∧ N x < Δ).
Unfold N, split, omega.
-/
theorem gap_empty (Δ : Nat) (x : Nat) : ¬(N Δ x > 0 ∧ N Δ x < Δ) := by
  sorry

#check @in_image_N
#check @zero_in_image
#check @observable_in_image
#check @gap_not_in_image
#check @N_idempotent
#check @N_projection
#check @N_triple
#check @fixed_point_iff
#check @N_range
#check @gap_empty
