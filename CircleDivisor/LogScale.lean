import CircleDivisor.BlockSeparation

/-! Actual logarithmic coordinates and the small logarithmic correction used
in the arithmetic case split. These are proved from mathlib asymptotics. -/

namespace CircleDivisor.LogScale
noncomputable section
open Filter Arithmetic ExternalInterfaces
open scoped Topology

def exponent (T x : ℝ) : ℝ := Real.log x / Real.log T

theorem rpow_exponent (T x : ℝ) (hT : 1 < T) (hx : 0 < x) :
    T ^ exponent T x = x := by
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  rw [Real.rpow_def_of_pos (by linarith)]
  have hh : Real.log T * exponent T x = Real.log x := by
    unfold exponent
    field_simp
  rw [hh, Real.exp_log hx]

theorem log_correction_tendsto :
    Tendsto (fun T : ℝ => exponent T (Real.log T)) atTop (𝓝 0) := by
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

theorem log_correction_eventually_small :
    ∀ᶠ T : ℝ in atTop, 0 ≤ exponent T (Real.log T) ∧
      exponent T (Real.log T) ≤ 1 / 100 := by
  have hu := log_correction_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hu, hl] with T hupper hlower
  exact ⟨div_nonneg (Real.log_nonneg hlower) (by linarith), hupper.le⟩

theorem blockLengthA_eq_power (T H M : ℝ) (hT : 1 < T) (hH : 0 < H) (hM : 0 < M) :
    blockLengthA H M T =
      T ^ blockA (exponent T H) (exponent T M) (exponent T (Real.log T)) := by
  have hTpos : 0 < T := by linarith
  have hlogpos : 0 < Real.log T := Real.log_pos hT
  unfold blockLengthA
  nth_rewrite 1 [← rpow_exponent T M hT hM]
  nth_rewrite 1 [← rpow_exponent T H hT hH]
  nth_rewrite 1 [← rpow_exponent T (Real.log T) hT hlogpos]
  simp only [← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos]
  congr 1
  unfold blockA
  ring

theorem blockLengthB_eq_power (T H M : ℝ) (hT : 1 < T) (hH : 0 < H) (hM : 0 < M) :
    blockLengthB H M T = T ^ min
      (blockB₁ (exponent T H) (exponent T M) (exponent T (Real.log T)))
      (blockB₂ (exponent T H) (exponent T M)) := by
  have hTpos : 0 < T := by linarith
  have hlogpos : 0 < Real.log T := Real.log_pos hT
  have hfirst : M ^ ((7 : ℝ) / 8) * H ^ (-(29 : ℝ) / 40) * T ^ (-(3 : ℝ) / 20) *
      (Real.log T) ^ ((969 : ℝ) / 5600) =
      T ^ blockB₁ (exponent T H) (exponent T M) (exponent T (Real.log T)) := by
    nth_rewrite 1 [← rpow_exponent T M hT hM]
    nth_rewrite 1 [← rpow_exponent T H hT hH]
    nth_rewrite 1 [← rpow_exponent T (Real.log T) hT hlogpos]
    simp only [← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos]
    congr 1
    unfold blockB₁
    ring
  have hsecond : M ^ (2 : ℝ) * H ^ (-(1 : ℝ) / 3) * T ^ (-(2 : ℝ) / 3) =
      T ^ blockB₂ (exponent T H) (exponent T M) := by
    nth_rewrite 1 [← rpow_exponent T M hT hM]
    nth_rewrite 1 [← rpow_exponent T H hT hH]
    simp only [← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos]
    congr 1
    unfold blockB₂
    ring
  unfold blockLengthB
  rw [hfirst, hsecond]
  rcases le_total
      (blockB₁ (exponent T H) (exponent T M) (exponent T (Real.log T)))
      (blockB₂ (exponent T H) (exponent T M)) with hab | hab
  · rw [min_eq_left hab, min_eq_left (Real.rpow_le_rpow_of_exponent_le hT.le hab)]
  · rw [min_eq_right hab, min_eq_right (Real.rpow_le_rpow_of_exponent_le hT.le hab)]

theorem radius_power_identity (T m n : ℝ) (hT : 0 < T) :
    (T ^ radiusExponent m n) ^ 2 * (T ^ n * T) = (T ^ m) ^ 3 := by
  have htwo : (T ^ radiusExponent m n) ^ 2 = T ^ (radiusExponent m n * 2) := by
    rw [Real.rpow_mul hT.le, Real.rpow_two]
  have hthree : (T ^ m) ^ 3 = T ^ (m * 3) := by
    rw [Real.rpow_mul hT.le]
    exact (Real.rpow_natCast _ 3).symm
  have hone : T ^ n * T = T ^ (n + 1) := by rw [Real.rpow_add hT, Real.rpow_one]
  rw [htwo, hthree, hone, ← Real.rpow_add hT]
  congr 1
  unfold radiusExponent
  ring

end
end CircleDivisor.LogScale
