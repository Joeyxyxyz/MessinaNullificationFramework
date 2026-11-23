/-
  NULLIFICATION BATCH 3: Distributivity & Accumulation
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
-- DISTRIBUTIVITY
-- ============================================================================

/--
PROVIDED SOLUTION: Unfold N. ha : a >= Δ means N a = a. hb : b >= Δ means N b = b.
So N a + N b = a + b.
-/
theorem distributive_when_both_survive (Δ : Nat) (a b : Nat) 
    (ha : a >= Δ) (hb : b >= Δ) :
    N Δ a + N Δ b = a + b := by
  sorry

/--
PROVIDED SOLUTION: a >= Δ and b >= Δ implies a + b >= Δ.
So N(a + b) = a + b.
-/
theorem distributive_sum_survives (Δ : Nat) (a b : Nat)
    (ha : a >= Δ) (hb : b >= Δ) :
    N Δ (a + b) = a + b := by
  sorry

/--
PROVIDED SOLUTION: Concrete example. N 10 (6 + 6) = N 10 12 = 12.
N 10 6 + N 10 6 = 0 + 0 = 0. 12 ≠ 0.
-/
theorem non_distributive_example : 
    N 10 (6 + 6) ≠ N 10 6 + N 10 6 := by
  sorry

/--
PROVIDED SOLUTION: Unfold N. 6 < 10 so N 10 6 = 0.
-/
theorem six_nullified : N 10 6 = 0 := by
  sorry

/--
PROVIDED SOLUTION: Unfold N. 12 >= 10 so N 10 12 = 12.
-/
theorem twelve_survives : N 10 12 = 12 := by
  sorry

-- ============================================================================
-- ACCUMULATION
-- ============================================================================

def sumR (Δ : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + R Δ x) 0

def sumN (Δ : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + N Δ x) 0

def sumList (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

/--
PROVIDED SOLUTION: Use exists with [3, 3, 3, 3]. Each 3 < 10 so nullified.
sumR = 3 + 3 + 3 + 3 = 12 >= 10.
-/
theorem accumulation_possible :
    ∃ (xs : List Nat), 
      (∀ x ∈ xs, classify 10 x = NullClass.nullified) ∧
      sumR 10 xs >= 10 := by
  sorry

/--
PROVIDED SOLUTION: Concrete computation. xs = [3,3,3,3,3].
Each N 10 3 = 0. sumR = 3+3+3+3+3 = 15. 15 >= 10.
-/
theorem five_threes_accumulate :
    let xs := [3, 3, 3, 3, 3]
    (∀ x ∈ xs, N 10 x = 0) ∧ sumR 10 xs = 15 ∧ sumR 10 xs >= 10 := by
  sorry

/--
PROVIDED SOLUTION: For empty list, all sums are 0. 0 + 0 = 0. ✓
-/
theorem list_conservation_empty (Δ : Nat) :
    sumN Δ [] + sumR Δ [] = sumList [] := by
  sorry

/--
PROVIDED SOLUTION: Single element. N x + R x = x by conservation.
sumN [x] = N x, sumR [x] = R x, sumList [x] = x.
-/
theorem list_conservation_singleton (Δ : Nat) (x : Nat) :
    sumN Δ [x] + sumR Δ [x] = sumList [x] := by
  sorry

/--
PROVIDED SOLUTION: Concrete: [3, 12] with Δ = 10.
N 10 3 = 0, N 10 12 = 12. sumN = 12.
R 10 3 = 3, R 10 12 = 0. sumR = 3.
sumList = 15. 12 + 3 = 15. ✓
-/
theorem list_conservation_example :
    sumN 10 [3, 12] + sumR 10 [3, 12] = sumList [3, 12] := by
  sorry

#check @distributive_when_both_survive
#check @distributive_sum_survives
#check @non_distributive_example
#check @six_nullified
#check @twelve_survives
#check @accumulation_possible
#check @five_threes_accumulate
#check @list_conservation_empty
#check @list_conservation_singleton
#check @list_conservation_example
