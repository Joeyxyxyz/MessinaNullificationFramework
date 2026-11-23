/-
  MNFCore.Hadamard — X-basis statistics from the amplitudes, core-only.

  Measuring every qubit in the X basis means applying H^{⊗n} and reading Z.
  Up to the overall factor 2^{−n/2}, H^{⊗n} acts on amplitude functions
  f : {0,1}^n → ℤ by the Walsh–Hadamard transform

      (had f)(s) = Σ_t (−1)^{s·t} f(t)          (s·t = number of shared 1s).

  GHZ_n and W_n both have integer (unnormalised) amplitudes, so their X-basis
  amplitudes are integers and the Born weights are the squares:

      had ghzAmp s = 1 + (−1)^{|s|}      (had_ghz)   ⟹  P_X(s) = (1+(−1)^{|s|})/2^n
      had wAmp   s = n − 2|s|            (had_w)     ⟹  P_X(s) = (n−2|s|)²/(n 2^n)

  with normalisation supplied by Parseval (parseval):  Σ_s (had f s)² = 2^n Σ_t f(t)².
  So the X-basis outcome sets used in MNFCore.GHZ (even-weight strings,
  equiprobable) are *derived* here from the state, not assumed.

  Consequences used by E1:
      ghz_x_support      : P_X(s) ≠ 0 ⟺ |s| even,  and all nonzero P_X equal
      ghz_x_prob         : P_X(s) = (1 + (−1)^{|s|}) / 2^n
      w_x_prob           : P_X(s) = (n − 2|s|)² / (n 2^n)
      w_x_single_{3,4,5,6} : ⟨X_k⟩ = 0 for W_n (kernel-checked instances; general n in MNFQ.Ladder)
      w_x_nbody_{3,4,5,6}  : ⟨X^{⊗n}⟩ = 0 for W_n (instances), and ≠ 0 for n = 2 (negative control)
      ⟨X^{⊗n}⟩ = 1 for GHZ_n is MNFCore.GHZ.ghz_x_parity / ghz_nbody_x
-/
import MNFCore.Bits
import MNFCore.WState
import MNFCore.GHZ

namespace MNF.Hadamard
open MNF.Bits

/-- Number of positions where both strings read 1. -/
def dot : List Bool → List Bool → Nat
  | b :: s, c :: t => (if b && c then 1 else 0) + dot s t
  | _, _ => 0

/-- (−1)^m. -/
def msign (m : Nat) : Int := if m % 2 = 0 then 1 else -1

/-- Unnormalised Walsh–Hadamard transform over all strings of length n. -/
def had (n : Nat) (f : List Bool → Int) (s : List Bool) : Int :=
  ((allStrings n).map (fun t => msign (dot s t) * f t)).sum

/-! ### Small algebra of signs and sums -/

theorem msign_add (a b : Nat) : msign (a + b) = msign a * msign b := by
  unfold msign; split <;> split <;> split <;> omega

theorem msign_zero : msign 0 = 1 := rfl
theorem msign_one : msign 1 = -1 := rfl
theorem msign_sq (m : Nat) : msign m * msign m = 1 := by unfold msign; split <;> rfl
theorem msign_bool (b : Bool) : msign (if b then 1 else 0) = sign b := by cases b <;> rfl

theorem sum_map_mul_left {α : Type} (L : List α) (c : Int) (g : α → Int) :
    (L.map (fun x => c * g x)).sum = c * (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]; grind

theorem sum_map_add {α : Type} (L : List α) (g h : α → Int) :
    (L.map (fun x => g x + h x)).sum = (L.map g).sum + (L.map h).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]; grind

theorem sum_map_zero {α : Type} (L : List α) : (L.map (fun _ => (0 : Int))).sum = 0 := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-- The transform only looks at f on `allStrings n`. -/
theorem had_congr (n : Nat) (f g : List Bool → Int) (s : List Bool)
    (h : ∀ t ∈ allStrings n, f t = g t) : had n f s = had n g s := by
  unfold had; congr 1
  apply List.map_congr_left; intro t ht; rw [h t ht]

theorem had_add (n : Nat) (f g : List Bool → Int) (s : List Bool) :
    had n (fun t => f t + g t) s = had n f s + had n g s := by
  unfold had
  rw [← sum_map_add]; congr 1
  apply List.map_congr_left; intro t _; grind

theorem had_zero (n : Nat) (s : List Bool) : had n (fun _ => 0) s = 0 := by
  unfold had; simp [sum_map_zero]

/-- Factorisation over the first bit: the tensor structure H ⊗ H^{⊗n}. -/
theorem had_succ (n : Nat) (f : List Bool → Int) (b : Bool) (s : List Bool) :
    had (n + 1) f (b :: s)
      = had n (fun t => f (false :: t)) s + sign b * had n (fun t => f (true :: t)) s := by
  unfold had
  rw [allStrings_succ, List.map_append, sum_append_int, List.map_map, List.map_map]
  have h1 : ((fun t => msign (dot (b :: s) t) * f t) ∘ (false :: ·))
      = (fun t => msign (dot s t) * f (false :: t)) := by
    funext t; simp [dot]
  have h2 : ((fun t => msign (dot (b :: s) t) * f t) ∘ (true :: ·))
      = (fun t => sign b * (msign (dot s t) * f (true :: t))) := by
    funext t; simp only [Function.comp, dot]
    rw [msign_add, msign_bool]; cases b <;> simp <;> grind
  rw [h1, h2, sum_map_mul_left]

/-! ### The two states -/

/-- Indicator of the all-zero string. -/
def deltaZeros (n : Nat) (t : List Bool) : Int := if t = zeros n then 1 else 0
/-- Indicator of the all-one string. -/
def deltaOnes (n : Nat) (t : List Bool) : Int := if t = ones n then 1 else 0
/-- Unnormalised GHZ amplitudes: 1 on 0^n and on 1^n. -/
def ghzAmp (n : Nat) (t : List Bool) : Int := deltaZeros n t + deltaOnes n t
/-- Unnormalised W amplitudes: 1 on every weight-1 string. -/
def wAmp (t : List Bool) : Int := if weight t = 1 then 1 else 0

theorem had_deltaZeros (n : Nat) (s : List Bool) (hs : s.length = n) :
    had n (deltaZeros n) s = 1 := by
  induction n generalizing s with
  | zero =>
    cases s with
    | nil => rfl
    | cons b t => simp at hs
  | succ n ih =>
    cases s with
    | nil => simp at hs
    | cons b s' =>
      rw [had_succ]
      have e1 : (fun t => deltaZeros (n + 1) (false :: t)) = deltaZeros n := by
        funext t; simp [deltaZeros]
      have e2 : (fun t => deltaZeros (n + 1) (true :: t)) = (fun _ => (0 : Int)) := by
        funext t; simp [deltaZeros]
      rw [e1, e2, had_zero, ih s' (by simpa using hs)]; simp

theorem had_deltaOnes (n : Nat) (s : List Bool) (hs : s.length = n) :
    had n (deltaOnes n) s = msign (weight s) := by
  induction n generalizing s with
  | zero =>
    cases s with
    | nil => rfl
    | cons b t => simp at hs
  | succ n ih =>
    cases s with
    | nil => simp at hs
    | cons b s' =>
      rw [had_succ]
      have e1 : (fun t => deltaOnes (n + 1) (false :: t)) = (fun _ => (0 : Int)) := by
        funext t; simp [deltaOnes]
      have e2 : (fun t => deltaOnes (n + 1) (true :: t)) = deltaOnes n := by
        funext t; simp [deltaOnes]
      rw [e1, e2, had_zero, ih s' (by simpa using hs)]
      rw [weight_cons, msign_add, msign_bool]; simp

/-- GHZ in the X basis: amplitude 1 + (−1)^{|s|}. -/
theorem had_ghz (n : Nat) (s : List Bool) (hs : s.length = n) :
    had n (ghzAmp n) s = 1 + msign (weight s) := by
  unfold ghzAmp
  rw [had_add, had_deltaZeros n s hs, had_deltaOnes n s hs]

/-- W in the X basis: amplitude n − 2|s|. -/
theorem had_w (n : Nat) (s : List Bool) (hs : s.length = n) :
    had n wAmp s = (n : Int) - 2 * weight s := by
  induction n generalizing s with
  | zero =>
    cases s with
    | nil => rfl
    | cons b t => simp at hs
  | succ n ih =>
    cases s with
    | nil => simp at hs
    | cons b s' =>
      rw [had_succ]
      have e1 : (fun t => wAmp (false :: t)) = wAmp := by funext t; simp [wAmp]
      -- on strings of length n, wAmp (true :: t) is the indicator of t = 0^n
      have e2 : had n (fun t => wAmp (true :: t)) s' = had n (deltaZeros n) s' := by
        apply had_congr; intro t ht
        have hlen := length_of_mem_allStrings ht
        simp only [wAmp, deltaZeros, weight_true_cons]
        by_cases h0 : weight t = 0
        · have := eq_zeros_of_weight_eq_zero h0
          rw [hlen] at this
          simp [this]
        · have : t ≠ zeros n := by
            intro h; apply h0; rw [h]; exact weight_zeros n
          simp [this]; omega
      rw [e1, e2, had_deltaZeros n s' (by simpa using hs), ih s' (by simpa using hs)]
      rw [weight_cons]; cases b <;> simp <;> omega

/-! ### Parseval: the transform preserves total weight up to 2^n -/

theorem parseval (n : Nat) (f : List Bool → Int) :
    ((allStrings n).map (fun s => had n f s * had n f s)).sum
      = 2 ^ n * ((allStrings n).map (fun t => f t * f t)).sum := by
  induction n generalizing f with
  | zero => simp [had, dot, msign]
  | succ n ih =>
    rw [allStrings_succ, List.map_append, sum_append_int, List.map_map, List.map_map]
    have hA : ((fun s => had (n + 1) f s * had (n + 1) f s) ∘ (false :: ·))
        = (fun s' => (had n (fun t => f (false :: t)) s' + had n (fun t => f (true :: t)) s')
                   * (had n (fun t => f (false :: t)) s' + had n (fun t => f (true :: t)) s')) := by
      funext s'; simp only [Function.comp]; rw [had_succ]; simp
    have hB : ((fun s => had (n + 1) f s * had (n + 1) f s) ∘ (true :: ·))
        = (fun s' => (had n (fun t => f (false :: t)) s' - had n (fun t => f (true :: t)) s')
                   * (had n (fun t => f (false :: t)) s' - had n (fun t => f (true :: t)) s')) := by
      funext s'; simp only [Function.comp]; rw [had_succ]; simp; grind
    rw [hA, hB, ← sum_map_add]
    have hsq : (fun s' => (had n (fun t => f (false :: t)) s' + had n (fun t => f (true :: t)) s')
                   * (had n (fun t => f (false :: t)) s' + had n (fun t => f (true :: t)) s')
                 + (had n (fun t => f (false :: t)) s' - had n (fun t => f (true :: t)) s')
                   * (had n (fun t => f (false :: t)) s' - had n (fun t => f (true :: t)) s'))
        = (fun s' => 2 * (had n (fun t => f (false :: t)) s' * had n (fun t => f (false :: t)) s'
                         + had n (fun t => f (true :: t)) s' * had n (fun t => f (true :: t)) s')) := by
      funext s'; grind
    rw [hsq, sum_map_mul_left, sum_map_add, ih, ih]
    -- right-hand side: split Σ_{t ∈ allStrings (n+1)} f t ^2 over the first bit
    rw [List.map_append, sum_append_int, List.map_map, List.map_map]
    have hR1 : ((fun t => f t * f t) ∘ (false :: ·)) = (fun t => f (false :: t) * f (false :: t)) := by
      funext t; rfl
    have hR2 : ((fun t => f t * f t) ∘ (true :: ·)) = (fun t => f (true :: t) * f (true :: t)) := by
      funext t; rfl
    rw [hR1, hR2, Int.pow_succ]; grind

/-! ### Normalisations of the two states (via the transform at s = 0^n) -/

theorem dot_zeros_left (n : Nat) (t : List Bool) : dot (zeros n) t = 0 := by
  induction n generalizing t with
  | zero => cases t <;> rfl
  | succ n ih => cases t with
    | nil => rfl
    | cons c t => simp [dot, ih]

/-- At s = 0^n the transform is the plain sum of the amplitudes. -/
theorem had_at_zeros (n : Nat) (f : List Bool → Int) :
    had n f (zeros n) = ((allStrings n).map f).sum := by
  unfold had; congr 1
  apply List.map_congr_left; intro t _; rw [dot_zeros_left, msign_zero]; simp

theorem wAmp_sq (t : List Bool) : wAmp t * wAmp t = wAmp t := by
  unfold wAmp; split <;> rfl

/-- W normalisation: Σ_t wAmp(t)² = n. -/
theorem w_norm (n : Nat) :
    ((allStrings n).map (fun t => wAmp t * wAmp t)).sum = n := by
  have : (allStrings n).map (fun t => wAmp t * wAmp t) = (allStrings n).map wAmp := by
    apply List.map_congr_left; intro t _; exact wAmp_sq t
  rw [this, ← had_at_zeros, had_w n (zeros n) (length_zeros n), weight_zeros]; simp

theorem zeros_ne_ones (n : Nat) (hn : 1 ≤ n) : zeros n ≠ ones n := by
  intro h
  have := congrArg weight h
  rw [weight_zeros, weight_ones] at this
  omega

theorem ghzAmp_sq (n : Nat) (hn : 1 ≤ n) (t : List Bool) :
    ghzAmp n t * ghzAmp n t = deltaZeros n t + deltaOnes n t := by
  unfold ghzAmp deltaZeros deltaOnes
  have hz : zeros n ≠ ones n := zeros_ne_ones n hn
  by_cases h0 : t = zeros n
  · subst h0; simp [hz]
  · by_cases h1 : t = ones n
    · subst h1; simp [Ne.symm hz]
    · simp [h0, h1]

/-- GHZ normalisation: Σ_t ghzAmp(t)² = 2 for n ≥ 1. -/
theorem ghz_norm (n : Nat) (hn : 1 ≤ n) :
    ((allStrings n).map (fun t => ghzAmp n t * ghzAmp n t)).sum = 2 := by
  have : (allStrings n).map (fun t => ghzAmp n t * ghzAmp n t)
      = (allStrings n).map (fun t => deltaZeros n t + deltaOnes n t) := by
    apply List.map_congr_left; intro t _; exact ghzAmp_sq n hn t
  rw [this, sum_map_add, ← had_at_zeros, ← had_at_zeros,
      had_deltaZeros n (zeros n) (length_zeros n), had_deltaOnes n (zeros n) (length_zeros n),
      weight_zeros, msign_zero]
  rfl

/-! ### Born weights -/

/-- GHZ: the squared X-basis amplitude is 2(1 + (−1)^{|s|}) — zero on odd strings,
    the same value 4 on every even string.  So the X-basis outcome set is the
    even-weight strings, equiprobable (the set used in MNFCore.GHZ). -/
theorem ghz_born_weight (n : Nat) (s : List Bool) (hs : s.length = n) :
    had n (ghzAmp n) s * had n (ghzAmp n) s = 2 * (1 + msign (weight s)) := by
  rw [had_ghz n s hs]
  have := msign_sq (weight s)
  grind

theorem ghz_x_support (n : Nat) (s : List Bool) (hs : s.length = n) :
    had n (ghzAmp n) s * had n (ghzAmp n) s ≠ 0 ↔ weight s % 2 = 0 := by
  rw [ghz_born_weight n s hs]; unfold msign
  by_cases h : weight s % 2 = 0 <;> simp [h]

/-- GHZ X-basis probability: (1 + (−1)^{|s|}) / 2^n. -/
theorem ghz_x_prob (n : Nat) (hn : 1 ≤ n) (s : List Bool) (hs : s.length = n) :
    ((had n (ghzAmp n) s * had n (ghzAmp n) s : Int) : Rat)
        / ((2 ^ n : Int) * ((allStrings n).map (fun t => ghzAmp n t * ghzAmp n t)).sum : Int)
      = ((1 + msign (weight s) : Int) : Rat) / (2 ^ n : Rat) := by
  rw [ghz_born_weight n s hs, ghz_norm n hn]
  push_cast
  have h2 : ((2 : Rat) ^ n) ≠ 0 := by
    have : (0 : Rat) < 2 ^ n := by exact_mod_cast Nat.two_pow_pos n
    exact Rat.ne_of_gt this
  rw [Rat.div_def, Rat.div_def]
  have hinv := Rat.mul_inv_cancel _ h2
  have h4 : ((2 : Rat) ^ n * 2) ≠ 0 := by grind
  have hinv2 := Rat.mul_inv_cancel _ h4
  grind

/-- W X-basis probability: (n − 2|s|)² / (n 2^n). -/
theorem w_x_prob (n : Nat) (s : List Bool) (hs : s.length = n) :
    ((had n wAmp s * had n wAmp s : Int) : Rat)
        / ((2 ^ n : Int) * ((allStrings n).map (fun t => wAmp t * wAmp t)).sum : Int)
      = (((n : Int) - 2 * weight s) * ((n : Int) - 2 * weight s) : Int) / ((2 ^ n : Int) * n : Int) := by
  rw [had_w n s hs, w_norm n]

/-! ### Kernel-checked tripwires for the W state in the X basis (instances n = 3..6)
  Σ_s (n−2|s|)² sign(s_k) = 0    ⟹ ⟨X_k⟩_W = 0   (reduced state diagonal)
  Σ_s (n−2|s|)² (−1)^{|s|} = 0  ⟹ ⟨X^{⊗n}⟩_W = 0 (no n-body X correlation)
  Both evaluated by the kernel over all 2^n strings; general n is in the Mathlib layer. -/

def wXsingle (n k : Nat) : Int :=
  ((allStrings n).map (fun s => had n wAmp s * had n wAmp s * sign (bitAt s k))).sum

def wXnbody (n : Nat) : Int :=
  ((allStrings n).map (fun s => had n wAmp s * had n wAmp s * msign (weight s))).sum

theorem w_x_single_3 : wXsingle 3 0 = 0 ∧ wXsingle 3 1 = 0 ∧ wXsingle 3 2 = 0 := by decide
theorem w_x_single_4 : wXsingle 4 0 = 0 ∧ wXsingle 4 1 = 0 ∧ wXsingle 4 2 = 0 ∧ wXsingle 4 3 = 0 := by decide
theorem w_x_single_5 : wXsingle 5 0 = 0 ∧ wXsingle 5 1 = 0 ∧ wXsingle 5 2 = 0 ∧
    wXsingle 5 3 = 0 ∧ wXsingle 5 4 = 0 := by decide
set_option maxRecDepth 200000 in
theorem w_x_single_6 : wXsingle 6 0 = 0 ∧ wXsingle 6 1 = 0 ∧ wXsingle 6 2 = 0 ∧
    wXsingle 6 3 = 0 ∧ wXsingle 6 4 = 0 ∧ wXsingle 6 5 = 0 := by decide
theorem w_x_nbody_3 : wXnbody 3 = 0 := by decide
theorem w_x_nbody_4 : wXnbody 4 = 0 := by decide
theorem w_x_nbody_5 : wXnbody 5 = 0 := by decide
set_option maxRecDepth 200000 in
theorem w_x_nbody_6 : wXnbody 6 = 0 := by decide
/-- Negative control: W_2 (a Bell-type state) *does* have an X-pair correlation (Σ = 8 ≠ 0). -/
theorem w_x_nbody_2_nonzero : wXnbody 2 ≠ 0 := by decide

end MNF.Hadamard
