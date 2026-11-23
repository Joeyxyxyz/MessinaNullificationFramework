/-
  MNFCore.GHZ — "the whole is observable, the parts are confined", core-only.

  |GHZ_n⟩ = (|0^n⟩ + |1^n⟩)/√2.

  Z basis: two equiprobable outcomes, 0^n and 1^n.
    ghz_z_single : Σ_s sign(s_k) = 0            ⟹ ⟨Z_k⟩ = 0      (each qubit: class [0])
    ghz_z_pair   : Σ_s sign(s_j) sign(s_k) = 2  ⟹ ⟨Z_j Z_k⟩ = 1  (perfect pair correlation)

  X basis: the 2^{n−1} even-weight strings, equiprobable (derived from the
  amplitudes in MNFCore.Hadamard; here taken as the outcome set).
    parityStrings_length : exactly 2^{n−1} outcomes                  (normalisation)
    ghz_x_balanced       : Σ_s sign(s_k) = 0 for n ≥ 2  ⟹ ⟨X_k⟩ = 0  (parts invisible)
    ghz_x_parity         : Σ_s (−1)^{|s|} = #outcomes   ⟹ ⟨X^{⊗n}⟩ = 1 (whole observable)

  Together with MNFCore.WState this is the E1 complementarity: every single-qubit
  Bloch vector of GHZ_n vanishes ([0]) while the n-body correlator is maximal ([1]);
  for W_n the single-qubit vectors are (0,0,(n−2)/n) and ⟨X^{⊗n}⟩ = 0.
-/
import MNFCore.Bits

namespace MNF.GHZ
open MNF.Bits

/-- Z-basis outcomes of GHZ_n. -/
def ghzZ (n : Nat) : List (List Bool) := [zeros n, ones n]

theorem ghzZ_length (n : Nat) : (ghzZ n).length = 2 := rfl

/-- ⟨Z_k⟩ = 0 for every qubit: the parts carry no Bloch vector. -/
theorem ghz_z_single (n k : Nat) (hk : k < n) : zSum (ghzZ n) k = 0 := by
  unfold ghzZ zSum; simp [bitAt_zeros, bitAt_ones n k hk]

/-- ⟨Z_j Z_k⟩ = 1 for every pair (unnormalised sum = 2 = number of outcomes). -/
theorem ghz_z_pair (n j k : Nat) (hj : j < n) (hk : k < n) : zzSum (ghzZ n) j k = 2 := by
  unfold ghzZ zzSum; simp [bitAt_zeros, bitAt_ones n j hj, bitAt_ones n k hk]

/-- Strings of a given weight parity p ∈ {0,1}, enumerated by filtering all strings. -/
def parityStrings (n p : Nat) : List (List Bool) :=
  (allStrings n).filter (fun s => decide (weight s % 2 = p))

/-- X-basis outcomes of GHZ_n: the even-weight strings. -/
def evenStrings (n : Nat) : List (List Bool) := parityStrings n 0

/-- Prepending a bit: `false` keeps the parity, `true` flips it. -/
theorem parityStrings_succ (n p : Nat) (hp : p < 2) :
    parityStrings (n + 1) p
      = (parityStrings n p).map (false :: ·) ++ (parityStrings n (1 - p)).map (true :: ·) := by
  unfold parityStrings
  rw [allStrings_succ, List.filter_append, List.filter_map, List.filter_map]
  have h1 : ((fun s => decide (weight s % 2 = p)) ∘ (false :: ·)) = (fun s => decide (weight s % 2 = p)) := by
    funext s; simp
  have h2 : ((fun s => decide (weight s % 2 = p)) ∘ (true :: ·)) = (fun s => decide (weight s % 2 = 1 - p)) := by
    funext s; simp; omega
  rw [h1, h2]

theorem parityStrings_one (p : Nat) (hp : p < 2) : (parityStrings 1 p).length = 1 := by
  match p, hp with
  | 0, _ => decide
  | 1, _ => decide

/-- Normalisation: 2^{n−1} strings of each parity (n ≥ 1). -/
theorem parityStrings_length (n : Nat) (hn : 1 ≤ n) (p : Nat) (hp : p < 2) :
    (parityStrings n p).length = 2 ^ (n - 1) := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simpa using parityStrings_one p hp
    | succ m =>
      rw [parityStrings_succ (m + 1) p hp]
      simp only [List.length_append, List.length_map]
      rw [ih (by omega) p hp, ih (by omega) (1 - p) (by omega)]
      simp [Nat.pow_succ]; omega

/-- Base case for the balance theorem: all four strings of length 2. -/
theorem balanced_two (k p : Nat) (hk : k < 2) (hp : p < 2) : zSum (parityStrings 2 p) k = 0 := by
  match k, hk, p, hp with
  | 0, _, 0, _ => decide
  | 0, _, 1, _ => decide
  | 1, _, 0, _ => decide
  | 1, _, 1, _ => decide

/-- Within each parity class, site k reads 1 exactly as often as 0 (n ≥ 2):
    Σ_s sign(s_k) = 0, hence ⟨X_k⟩ = 0 in the X basis of GHZ_n. -/
theorem ghz_x_balanced (n : Nat) (hn : 2 ≤ n) (k : Nat) (hk : k < n) (p : Nat) (hp : p < 2) :
    zSum (parityStrings n p) k = 0 := by
  induction n generalizing k p with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => exact balanced_two k p hk hp
      | succ m =>
        rw [parityStrings_succ (m + 2) p hp, zSum_append]
        cases k with
        | zero =>
          rw [zSum_map_cons_zero, zSum_map_cons_zero,
              parityStrings_length (m + 2) (by omega) p hp,
              parityStrings_length (m + 2) (by omega) (1 - p) (by omega)]
          simp <;> omega
        | succ k =>
          rw [zSum_map_cons_succ, zSum_map_cons_succ,
              ih (by omega) k (by omega) p hp, ih (by omega) k (by omega) (1 - p) (by omega)]
          rfl

/-- Every even-weight string has parity sign +1, so the n-body correlator sums to the count:
    ⟨X^{⊗n}⟩ = 1. -/
theorem ghz_x_parity (n : Nat) : paritySum (evenStrings n) = (evenStrings n).length := by
  unfold paritySum
  have hmap : (evenStrings n).map paritySign = (evenStrings n).map (fun _ => (1 : Int)) := by
    apply List.map_congr_left
    intro s hs
    unfold evenStrings parityStrings at hs
    have := (List.mem_filter.mp hs).2
    simp at this
    unfold paritySign; simp [this]
  rw [hmap, sum_map_const_int]; simp

/-! ### Normalised statements -/

theorem ghz_bloch_z (n k : Nat) (hk : k < n) :
    (zSum (ghzZ n) k : Rat) / (ghzZ n).length = 0 := by
  rw [ghz_z_single n k hk]; rw [Rat.div_def]; grind

theorem ghz_pair_corr (n j k : Nat) (hj : j < n) (hk : k < n) :
    (zzSum (ghzZ n) j k : Rat) / (ghzZ n).length = 1 := by
  rw [ghz_z_pair n j k hj hk, ghzZ_length]; grind

theorem ghz_bloch_x (n : Nat) (hn : 2 ≤ n) (k : Nat) (hk : k < n) :
    (zSum (evenStrings n) k : Rat) / (evenStrings n).length = 0 := by
  unfold evenStrings
  rw [ghz_x_balanced n hn k hk 0 (by omega)]; rw [Rat.div_def]; grind

theorem ghz_nbody_x (n : Nat) (hn : 1 ≤ n) :
    (paritySum (evenStrings n) : Rat) / (evenStrings n).length = 1 := by
  rw [ghz_x_parity n]
  have hlen : (evenStrings n).length = 2 ^ (n - 1) := parityStrings_length n hn 0 (by omega)
  have hpos : (0 : Rat) < ((evenStrings n).length : Rat) := by
    rw [hlen]; exact_mod_cast Nat.two_pow_pos (n - 1)
  have hne : ((evenStrings n).length : Rat) ≠ 0 := Rat.ne_of_gt hpos
  rw [Rat.div_def]; exact Rat.mul_inv_cancel _ hne

end MNF.GHZ
