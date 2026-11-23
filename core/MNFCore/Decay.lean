/-
  MNFCore.Decay — the threshold time of a confined qubit under relaxation, core-only.

  Experiment E3.  A qubit that is one half of a Bell pair has reduced state I/2:
  Bloch length 0, class [0].  Left idle, amplitude damping (T1) pulls it toward
  |0⟩, so ⟨Z⟩ rises from 0 toward the plateau z∞ (= 1 for a perfect, cold
  device; slightly less with thermal population and readout error).  With the
  declared threshold Δ = 1/2 on the Bloch length, the qubit crosses from the
  reservoir class [0.0e] into the observable class [1] when ⟨Z⟩ = 1/2.

  Model.  ⟨Z⟩(t) = z∞ + (z₀ − z∞) q(t), where q(t) ∈ (0,1] is the survival
  factor (q = e^{−t/T1} physically).  All that is used here is the memoryless
  (semigroup) law q(s + t) = q(s) q(t) and monotonicity; the identification
  q = e^{−t/T1}, hence t* = T1 ln 2, is in the Mathlib layer (MNFQ.Decay).

  Results (all over ℚ, kernel-checked):
    bell_crossing_iff   : Bell partner (z₀ = 0, z∞ = 1) hits 1/2  ⟺  q = 1/2
    one_crossing_iff    : |1⟩ baseline (z₀ = −1, z∞ = 1) hits 1/2 ⟺  q = 1/4
    ratio_two           : if the Bell partner crosses at t*, the |1⟩ baseline
                          crosses at exactly t* + t* = 2 t*   (T1-independent)
    bell_crossing_general / one_crossing_general : the same with plateau z∞
    bell_increasing     : ⟨Z⟩ of the Bell partner is strictly increasing as q
                          decays (the trajectory is [0] → [0.0e] → [1], once)
    bell_class_*        : the classification along the trajectory
    zero_flat           : the |0⟩ baseline is flat at the plateau
-/
import MNFCore.Operator

namespace MNF.Decay

/-- ⟨Z⟩ after relaxation with plateau z∞, initial value z₀ and survival factor q. -/
def z (zinf z0 q : Rat) : Rat := zinf + (z0 - zinf) * q

/-- Bell partner: z₀ = 0. -/
theorem bell_traj (zinf q : Rat) : z zinf 0 q = zinf * (1 - q) := by unfold z; grind
/-- |1⟩ baseline: z₀ = −1. -/
theorem one_traj (zinf q : Rat) : z zinf (-1) q = zinf - (1 + zinf) * q := by unfold z; grind
/-- |0⟩ baseline: z₀ = 1. -/
theorem zero_traj (zinf q : Rat) : z zinf 1 q = zinf + (1 - zinf) * q := by unfold z; grind

/-- With a perfect plateau the |0⟩ baseline never moves. -/
theorem zero_flat (q : Rat) : z 1 1 q = 1 := by unfold z; grind

/-- Bell partner crosses Δ = 1/2 exactly when half of the survival factor is gone. -/
theorem bell_crossing_iff (q : Rat) : z 1 0 q = 1 / 2 ↔ q = 1 / 2 := by
  unfold z; constructor <;> intro h <;> grind

/-- |1⟩ baseline crosses Δ = 1/2 exactly when q = 1/4. -/
theorem one_crossing_iff (q : Rat) : z 1 (-1) q = 1 / 2 ↔ q = 1 / 4 := by
  unfold z; constructor <;> intro h <;> grind

/-- Memoryless decay doubles the time: if the Bell partner crosses at t*, the |1⟩
    baseline crosses at t* + t*.  No rate constant appears. -/
theorem ratio_two (q : Rat → Rat) (hq : ∀ s t, q (s + t) = q s * q t)
    (tstar : Rat) (hstar : q tstar = 1 / 2) : z 1 (-1) (q (tstar + tstar)) = 1 / 2 := by
  rw [hq tstar tstar, hstar]; unfold z; grind

/-- The survival factor at t* + t* is exactly 1/4.  (That 2 t* is the *only* crossing time
    needs injectivity of q in t, i.e. strict monotonicity of the physical q = e^{−t/T1};
    that step is in the Mathlib layer, `MNFQ.Decay.one_crossing_unique`.) -/
theorem one_crossing_value (q : Rat → Rat) (hq : ∀ s t, q (s + t) = q s * q t)
    (tstar : Rat) (hstar : q tstar = 1 / 2) : q (tstar + tstar) = 1 / 4 := by
  rw [hq tstar tstar, hstar]; grind

/-- General plateau z∞ > 1/2: Bell partner crosses at q* = 1 − 1/(2 z∞). -/
theorem bell_crossing_general (zinf q : Rat) (hz : 1 / 2 < zinf) :
    z zinf 0 q = 1 / 2 ↔ q = 1 - 1 / (2 * zinf) := by
  have hne : zinf ≠ 0 := by grind
  have h2 : (2 * zinf) ≠ 0 := by grind
  unfold z; constructor <;> intro h
  · -- zinf (1 − q) = 1/2  ⟹  q = 1 − 1/(2 zinf)
    have : zinf * q = zinf - 1 / 2 := by grind
    have hinv := Rat.mul_inv_cancel (2 * zinf) h2
    rw [Rat.div_def]; grind
  · rw [Rat.div_def] at h
    have hinv := Rat.mul_inv_cancel (2 * zinf) h2
    subst h; grind

/-- General plateau: |1⟩ baseline crosses at q* = (z∞ − 1/2)/(1 + z∞). -/
theorem one_crossing_general (zinf q : Rat) (hz : 1 / 2 < zinf) :
    z zinf (-1) q = 1 / 2 ↔ q = (zinf - 1 / 2) / (1 + zinf) := by
  have h1 : (1 + zinf) ≠ 0 := by grind
  have hinv := Rat.mul_inv_cancel (1 + zinf) h1
  unfold z; constructor <;> intro h
  · rw [Rat.div_def]; grind
  · rw [Rat.div_def] at h; subst h; grind

/-- As q decays (q₂ < q₁) the Bell partner's ⟨Z⟩ strictly increases: it leaves [0],
    passes through [0.0e] and enters [1] once, never returning. -/
theorem bell_increasing (zinf q₁ q₂ : Rat) (hz : 0 < zinf) (h : q₂ < q₁) :
    z zinf 0 q₁ < z zinf 0 q₂ := by
  unfold z
  have := Rat.mul_lt_mul_of_pos_left h hz
  grind

/-- Classification of the Bell partner along its trajectory (perfect plateau). -/
theorem bell_class_start : MNF.classifyQ (1 / 2) (z 1 0 1) = .zero := by
  have : z 1 0 1 = 0 := by unfold z; grind
  rw [this]; exact MNF.classifyQ_zero _

theorem bell_class_reservoir (q : Rat) (h1 : 1 / 2 < q) (h2 : q < 1) :
    MNF.classifyQ (1 / 2) (z 1 0 q) = .reservoir := by
  apply MNF.classifyQ_reservoir
  · unfold z; grind
  · unfold z; grind

theorem bell_class_observable (q : Rat) (h1 : q ≤ 1 / 2) :
    MNF.classifyQ (1 / 2) (z 1 0 q) = .observable := by
  apply MNF.classifyQ_observable
  · unfold z; grind
  · unfold z; grind

/-- The crossing is the boundary: at q = 1/2 the partner is exactly at Δ (observable by
    R(Δ,Δ) = 0), and for every q > 1/2 it is still in the reservoir. -/
theorem bell_at_threshold : z 1 0 (1 / 2) = 1 / 2 := by unfold z; grind

end MNF.Decay
