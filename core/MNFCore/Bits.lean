/-
  MNFCore.Bits — bitstrings (measurement outcomes) as `List Bool`, core-only.

  A Z-basis (or X-, Y-basis) readout of n qubits is a bitstring of length n.
  `allStrings n` enumerates all 2^n of them; `weight` counts the 1s; `bitAt s k`
  reads qubit k; `sign` turns a bit into the ±1 eigenvalue used in expectation
  values.  `zSum L k = Σ_{s ∈ L} sign (bitAt s k)` is the (unnormalised)
  expectation of the k-th Pauli in the measured basis when the outcomes in L are
  equiprobable; dividing by `L.length` gives the expectation value.

  Convention: `bitAt s 0` is the first list entry.  (In the circuit package qubit
  k is the (k+1)-th character from the right of a Qiskit bitstring; the analysis
  script applies that reversal.  Nothing here depends on which end is "first".)
-/

namespace MNF.Bits

/-- All bitstrings of length n, in a fixed order (2^n of them). -/
def allStrings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allStrings n).map (false :: ·) ++ (allStrings n).map (true :: ·)

/-- Hamming weight. -/
def weight : List Bool → Nat
  | [] => 0
  | b :: s => (if b then 1 else 0) + weight s

/-- The bit at position k (false beyond the end). -/
def bitAt (s : List Bool) (k : Nat) : Bool := s.getD k false

/-- ±1 eigenvalue of a readout bit. -/
def sign (b : Bool) : Int := if b then -1 else 1

/-- Unnormalised single-site expectation over a list of equiprobable outcomes. -/
def zSum (L : List (List Bool)) (k : Nat) : Int := (L.map (fun s => sign (bitAt s k))).sum

/-- Unnormalised two-site correlator. -/
def zzSum (L : List (List Bool)) (j k : Nat) : Int :=
  (L.map (fun s => sign (bitAt s j) * sign (bitAt s k))).sum

/-- Parity sign (−1)^{weight s}: the n-body correlator of one outcome. -/
def paritySign (s : List Bool) : Int := if weight s % 2 = 0 then 1 else -1

/-- Unnormalised n-body correlator. -/
def paritySum (L : List (List Bool)) : Int := (L.map paritySign).sum

/-- The all-zero string. -/
def zeros (n : Nat) : List Bool := List.replicate n false
/-- The all-one string. -/
def ones (n : Nat) : List Bool := List.replicate n true

/-! ### Basic facts -/

/-- Integer list sums split over `++` (core only ships the ℕ version). -/
theorem sum_append_int (l₁ l₂ : List Int) : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sum_map_const_int {α : Type} (L : List α) (c : Int) :
    (L.map (fun _ => c)).sum = (L.length : Int) * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]; grind

@[simp] theorem allStrings_zero : allStrings 0 = [[]] := rfl
theorem allStrings_succ (n : Nat) :
    allStrings (n + 1) = (allStrings n).map (false :: ·) ++ (allStrings n).map (true :: ·) := rfl

@[simp] theorem weight_nil : weight [] = 0 := rfl
@[simp] theorem weight_cons (b : Bool) (s : List Bool) :
    weight (b :: s) = (if b then 1 else 0) + weight s := rfl
@[simp] theorem weight_false_cons (s : List Bool) : weight (false :: s) = weight s := by simp
@[simp] theorem weight_true_cons (s : List Bool) : weight (true :: s) = 1 + weight s := by simp

@[simp] theorem bitAt_cons_zero (b : Bool) (s : List Bool) : bitAt (b :: s) 0 = b := rfl
@[simp] theorem bitAt_cons_succ (b : Bool) (s : List Bool) (k : Nat) :
    bitAt (b :: s) (k + 1) = bitAt s k := rfl
@[simp] theorem bitAt_nil (k : Nat) : bitAt [] k = false := by
  unfold bitAt; simp

@[simp] theorem sign_true : sign true = -1 := rfl
@[simp] theorem sign_false : sign false = 1 := rfl

theorem allStrings_length (n : Nat) : (allStrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allStrings_succ, ih, Nat.pow_succ]; omega

theorem length_of_mem_allStrings {n : Nat} {s : List Bool} (h : s ∈ allStrings n) : s.length = n := by
  induction n generalizing s with
  | zero => simp [allStrings_zero] at h; simp [h]
  | succ n ih =>
    simp only [allStrings_succ, List.mem_append, List.mem_map] at h
    rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;> simp [ih ht]

theorem mem_allStrings_of_length {n : Nat} {s : List Bool} (h : s.length = n) : s ∈ allStrings n := by
  induction n generalizing s with
  | zero => cases s with
    | nil => simp
    | cons b t => simp at h
  | succ n ih =>
    cases s with
    | nil => simp at h
    | cons b t =>
      simp only [List.length_cons] at h
      have ht : t ∈ allStrings n := ih (by omega)
      simp only [allStrings_succ, List.mem_append, List.mem_map]
      cases b
      · exact Or.inl ⟨t, ht, rfl⟩
      · exact Or.inr ⟨t, ht, rfl⟩

@[simp] theorem zeros_zero : zeros 0 = [] := rfl
@[simp] theorem zeros_succ (n : Nat) : zeros (n + 1) = false :: zeros n := rfl
@[simp] theorem ones_zero : ones 0 = [] := rfl
@[simp] theorem ones_succ (n : Nat) : ones (n + 1) = true :: ones n := rfl

@[simp] theorem weight_zeros (n : Nat) : weight (zeros n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

@[simp] theorem weight_ones (n : Nat) : weight (ones n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]; omega

@[simp] theorem bitAt_zeros (n k : Nat) : bitAt (zeros n) k = false := by
  induction n generalizing k with
  | zero => simp
  | succ n ih => cases k <;> simp [ih]

@[simp] theorem bitAt_ones (n k : Nat) (hk : k < n) : bitAt (ones n) k = true := by
  induction n generalizing k with
  | zero => omega
  | succ n ih => cases k with
    | zero => simp
    | succ k => simp [ih k (by omega)]

theorem length_zeros (n : Nat) : (zeros n).length = n := by simp [zeros]
theorem length_ones (n : Nat) : (ones n).length = n := by simp [ones]

/-- The only weight-0 string of length n is `zeros n`. -/
theorem eq_zeros_of_weight_eq_zero {s : List Bool} (h : weight s = 0) : s = zeros s.length := by
  induction s with
  | nil => rfl
  | cons b t ih =>
    cases b
    · have h' : weight t = 0 := by simpa using h
      have := ih h'
      simp only [List.length_cons, zeros_succ]
      rw [← this]
    · simp at h

/-- zSum and zzSum over appended lists. -/
theorem zSum_append (L M : List (List Bool)) (k : Nat) :
    zSum (L ++ M) k = zSum L k + zSum M k := by
  unfold zSum; simp [List.map_append, sum_append_int]

theorem zSum_nil (k : Nat) : zSum [] k = 0 := rfl
theorem zSum_cons (s : List Bool) (L : List (List Bool)) (k : Nat) :
    zSum (s :: L) k = sign (bitAt s k) + zSum L k := rfl

theorem paritySum_append (L M : List (List Bool)) :
    paritySum (L ++ M) = paritySum L + paritySum M := by
  unfold paritySum; simp [List.map_append, sum_append_int]

/-- Prepending a bit shifts the site index. -/
theorem zSum_map_cons_succ (b : Bool) (L : List (List Bool)) (k : Nat) :
    zSum (L.map (b :: ·)) (k + 1) = zSum L k := by
  unfold zSum; simp [List.map_map, Function.comp_def]

/-- At site 0, every prepended string contributes the same sign. -/
theorem zSum_map_cons_zero (b : Bool) (L : List (List Bool)) :
    zSum (L.map (b :: ·)) 0 = (L.length : Int) * sign b := by
  unfold zSum
  induction L with
  | nil => simp
  | cons s L ih => simp; grind

end MNF.Bits
