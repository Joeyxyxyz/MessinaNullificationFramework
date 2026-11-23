/-
  MNFCore.WState — Z-basis statistics of the W state, core-only.

  |W_n⟩ = n^{-1/2} Σ_j |e_j⟩.  Its Z-basis readout is "exactly one qubit reads 1,
  each position equally likely": the outcome set is the weight-1 strings, each
  with probability 1/n.  Everything below is a statement about that outcome set,
  obtained here by *filtering all 2^n strings* (so nothing is hand-picked):

    wSupport_length   : there are exactly n outcomes          (normalisation)
    w_zSum            : Σ_s sign(s_k) = n − 2                 (so ⟨Z_k⟩ = (n−2)/n)
    w_zzSum           : Σ_s sign(s_j) sign(s_k) = n − 4       (so ⟨Z_j Z_k⟩ = (n−4)/n)
    w_bloch_z         : ⟨Z_k⟩ = (n−2)/n as a rational number
    w_class_*         : classification at Δ = 1/2 along the ladder n = 2,3,4,…
    w_crossing_iff    : ⟨Z_k⟩ ≥ 1/2  ↔  n ≥ 4        (the threshold crossing)
    w_at_threshold    : n = 4 sits exactly on Δ      (R(Δ,Δ) = 0: observable)
    w_monotone        : the ladder is strictly increasing in n
    w_pair_vanishes_at_threshold : ⟨Z_j Z_k⟩ = 0 exactly at n = 4

  The amplitude-level fact that the W state's Z-basis distribution *is* this
  outcome set (Born rule) is standard and is re-derived numerically in
  sim/verify_predictions.py; the X-basis distribution is derived from the
  amplitudes in MNFCore.Hadamard.

  Experiment E1 reads ⟨Z_k⟩ (and ⟨X_k⟩, ⟨Y_k⟩ = 0, see Hadamard) on hardware for
  n = 3..8 and tests the classification sequence against these theorems.
-/
import MNFCore.Bits
import MNFCore.Operator

namespace MNF.WState
open MNF.Bits

/-- Z-basis outcomes of W_n: the weight-1 strings among all strings of length n. -/
def wSupport (n : Nat) : List (List Bool) :=
  (allStrings n).filter (fun s => decide (weight s = 1))

/-- Among all strings of length n, exactly one has weight 0: the all-zero string. -/
theorem filter_weight_zero (n : Nat) :
    (allStrings n).filter (fun s => decide (weight s = 0)) = [zeros n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allStrings_succ, List.filter_append, List.filter_map, List.filter_map]
    have h1 : ((fun s => decide (weight s = 0)) ∘ (false :: ·)) = (fun s => decide (weight s = 0)) := by
      funext s; simp
    have h2 : ((fun s => decide (weight s = 0)) ∘ (true :: ·)) = (fun _ => false) := by
      funext s; simp
    rw [h1, h2, ih]
    simp

/-- Recursive structure of the W outcome set. -/
theorem wSupport_succ (n : Nat) :
    wSupport (n + 1) = (wSupport n).map (false :: ·) ++ [true :: zeros n] := by
  unfold wSupport
  rw [allStrings_succ, List.filter_append, List.filter_map, List.filter_map]
  have h1 : ((fun s => decide (weight s = 1)) ∘ (false :: ·)) = (fun s => decide (weight s = 1)) := by
    funext s; simp
  have h2 : ((fun s => decide (weight s = 1)) ∘ (true :: ·)) = (fun s => decide (weight s = 0)) := by
    funext s; simp
  rw [h1, h2, filter_weight_zero]
  rfl

theorem wSupport_zero : wSupport 0 = [] := rfl

/-- Normalisation: W_n has exactly n Z-basis outcomes (each of probability 1/n). -/
theorem wSupport_length (n : Nat) : (wSupport n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wSupport_succ]; simp [ih]

/-- Every outcome has weight 1 (one excitation). -/
theorem weight_of_mem_wSupport {n : Nat} {s : List Bool} (h : s ∈ wSupport n) : weight s = 1 := by
  unfold wSupport at h
  have := (List.mem_filter.mp h).2
  simpa using this

/-- Σ_{s ∈ wSupport n} sign(s_k) = n − 2 for every site k < n.
    Hence ⟨Z_k⟩ = (n − 2)/n: the single-qubit Bloch vector of W_n is (0,0,(n−2)/n). -/
theorem w_zSum (n k : Nat) (hk : k < n) : zSum (wSupport n) k = (n : Int) - 2 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    rw [wSupport_succ, zSum_append]
    cases k with
    | zero =>
      rw [zSum_map_cons_zero, wSupport_length]
      simp [zSum_cons, zSum_nil]
      omega
    | succ k =>
      rw [zSum_map_cons_succ, ih k (by omega)]
      simp [zSum_cons, zSum_nil]
      omega

/-- Two-site correlator: Σ_s sign(s_j) sign(s_k) = n − 4 for j ≠ k.
    Hence ⟨Z_j Z_k⟩ = (n − 4)/n. -/
theorem w_zzSum (n j k : Nat) (hj : j < n) (hk : k < n) (hjk : j ≠ k) :
    zzSum (wSupport n) j k = (n : Int) - 4 := by
  induction n generalizing j k with
  | zero => omega
  | succ n ih =>
    rw [wSupport_succ]
    unfold zzSum
    rw [List.map_append, sum_append_int, List.map_map]
    cases j with
    | zero =>
      cases k with
      | zero => exact absurd rfl hjk
      | succ k =>
        -- site 0 is false on every mapped string; site k+1 reads site k of the original
        have hfirst : ((wSupport n).map ((fun s => sign (bitAt s 0) * sign (bitAt s (k + 1))) ∘ (false :: ·))).sum
            = zSum (wSupport n) k := by
          unfold zSum; congr 1
          try (apply List.map_congr_left; intro s _; simp)
        rw [hfirst, w_zSum n k (by omega)]
        simp [bitAt_zeros] <;> omega
    | succ j =>
      cases k with
      | zero =>
        have hfirst : ((wSupport n).map ((fun s => sign (bitAt s (j + 1)) * sign (bitAt s 0)) ∘ (false :: ·))).sum
            = zSum (wSupport n) j := by
          unfold zSum; congr 1
          try (apply List.map_congr_left; intro s _; simp)
        rw [hfirst, w_zSum n j (by omega)]
        simp [bitAt_zeros] <;> omega
      | succ k =>
        have hfirst : ((wSupport n).map ((fun s => sign (bitAt s (j + 1)) * sign (bitAt s (k + 1))) ∘ (false :: ·))).sum
            = zzSum (wSupport n) j k := by
          unfold zzSum; congr 1
          try (apply List.map_congr_left; intro s _; simp)
        have hjk' : j ≠ k := fun h => hjk (by rw [h])
        rw [hfirst, ih j k (by omega) (by omega) hjk']
        simp [bitAt_zeros] <;> omega

/-! ### Rational-valued statements used by the pre-registration -/

/-- ⟨Z_k⟩ = (n − 2)/n exactly. -/
theorem w_bloch_z (n k : Nat) (hk : k < n) :
    (zSum (wSupport n) k : Rat) / (wSupport n).length = ((n : Rat) - 2) / n := by
  rw [w_zSum n k hk, wSupport_length]
  push_cast; rfl

/-- ⟨Z_j Z_k⟩ = (n − 4)/n exactly. -/
theorem w_pair_corr (n j k : Nat) (hj : j < n) (hk : k < n) (hjk : j ≠ k) :
    (zzSum (wSupport n) j k : Rat) / (wSupport n).length = ((n : Rat) - 4) / n := by
  rw [w_zzSum n j k hj hk hjk, wSupport_length]
  push_cast; rfl

/-- The Bloch z-component of W_n, as a rational function of n. -/
def wBloch (n : Nat) : Rat := ((n : Rat) - 2) / n

/-- Helper: 1/2 ≤ (n−2)/n when n ≤ 2(n−2) and n > 0. -/
theorem half_le_frac (n : Rat) (hpos : 0 < n) (h : n ≤ 2 * (n - 2)) : (1 : Rat) / 2 ≤ (n - 2) / n := by
  have hne : n ≠ 0 := by grind
  have h1 : n * ((n - 2) / n) = n - 2 := by rw [Rat.div_def]; grind
  have h2 : n * (1 / 2) ≤ n * ((n - 2) / n) := by rw [h1]; grind
  exact Rat.le_of_mul_le_mul_left h2 hpos

theorem frac_lt_half (n : Rat) (hpos : 0 < n) (h : 2 * (n - 2) < n) : (n - 2) / n < (1 : Rat) / 2 := by
  rw [Rat.div_lt_iff hpos]; grind

/-- The ladder crosses Δ = 1/2 exactly at n = 4: ⟨Z_k⟩ ≥ 1/2 ↔ n ≥ 4. -/
theorem w_crossing_iff (n : Nat) (hn : 0 < n) : (1 : Rat) / 2 ≤ wBloch n ↔ 4 ≤ n := by
  unfold wBloch
  have hpos : (0 : Rat) < n := by exact_mod_cast hn
  constructor
  · intro h
    by_cases h4 : 4 ≤ n
    · exact h4
    · have hlt : (n : Rat) < 4 := by exact_mod_cast (by omega : n < 4)
      have := frac_lt_half n hpos (by grind)
      exact absurd h (Rat.not_le.mpr this)
  · intro h4
    have h4' : (4 : Rat) ≤ n := by exact_mod_cast h4
    exact half_le_frac n hpos (by grind)

/-- n = 2: both qubits of W_2 (a Bell-type state) are confined, class [0]. -/
theorem w_class_two : MNF.classifyQ (1 / 2) (wBloch 2) = .zero := by
  have h : wBloch 2 = 0 := by unfold wBloch; grind
  rw [h]; exact MNF.classifyQ_zero _

/-- n = 3: |r| = 1/3 < 1/2, class [0.0e] (reservoir). -/
theorem w_class_three : MNF.classifyQ (1 / 2) (wBloch 3) = .reservoir := by
  unfold wBloch
  apply MNF.classifyQ_reservoir
  · grind
  · grind

/-- n = 4: |r| = 1/2 = Δ exactly; by R(Δ,Δ) = 0 the state is observable, class [1]. -/
theorem w_at_threshold : wBloch 4 = 1 / 2 := by unfold wBloch; grind

theorem w_class_four : MNF.classifyQ (1 / 2) (wBloch 4) = .observable := by
  rw [w_at_threshold]
  apply MNF.classifyQ_observable
  · grind
  · exact Rat.le_refl

/-- n ≥ 4: class [1]. -/
theorem w_class_ge_four (n : Nat) (hn : 4 ≤ n) : MNF.classifyQ (1 / 2) (wBloch n) = .observable := by
  have hpos : (0 : Rat) < n := by exact_mod_cast (by omega : 0 < n)
  have h4' : (4 : Rat) ≤ n := by exact_mod_cast hn
  apply MNF.classifyQ_observable
  · unfold wBloch
    intro h0
    rw [Rat.div_def] at h0
    rcases Rat.mul_eq_zero.mp h0 with h | h
    · grind
    · grind
  · exact (w_crossing_iff n (by omega)).mpr hn

/-- The ladder is strictly increasing: (n−2)/n < (n−1)/(n+1) for n ≥ 1. -/
theorem w_monotone (n : Nat) (hn : 1 ≤ n) : wBloch n < wBloch (n + 1) := by
  unfold wBloch
  have hpos : (0 : Rat) < n := by exact_mod_cast hn
  have hpos' : (0 : Rat) < (n : Rat) + 1 := by grind
  push_cast
  rw [Rat.div_lt_iff hpos]
  -- (n−2) < ((n+1−2)/(n+1)) · n  ⟺  (n−2)(n+1) < (n−1) n
  have key : ((n : Rat) + 1 - 2) / ((n : Rat) + 1) * n = ((n : Rat) - 1) * n / ((n : Rat) + 1) := by
    rw [Rat.div_def, Rat.div_def]; grind
  rw [key, Rat.lt_div_iff hpos']
  grind

/-- ⟨Z_j Z_k⟩ vanishes exactly on the threshold rung n = 4. -/
theorem w_pair_vanishes_at_threshold (n : Nat) (hn : 0 < n) :
    ((n : Rat) - 4) / n = 0 ↔ n = 4 := by
  have hne : (n : Rat) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  constructor
  · intro h
    rw [Rat.div_def] at h
    rcases Rat.mul_eq_zero.mp h with h | h
    · have : (n : Rat) = 4 := by grind
      exact_mod_cast this
    · grind
  · intro h; subst h; grind

end MNF.WState
