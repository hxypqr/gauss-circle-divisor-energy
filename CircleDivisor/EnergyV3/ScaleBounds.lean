import CircleDivisor.EnergyV3.ScaleExponents
import CircleDivisor.EnergyV3.Arithmetic
import CircleDivisor.ScaleBounds

/-! Real-parameter scale estimates with the revised cross-ray energy and
the improved third monomial. All constants are uniform for `4 ≤ q ≤ 9/2`. -/

namespace CircleDivisor.EnergyV3.ScaleBounds
noncomputable section
open CircleDivisor.ScaleBounds CircleDivisor.ScaleExponents

theorem cross_energy_le_exp {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    min ((K * L) * M K L s) (K ^ 2 * L + s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) ≤
      4 * Real.exp (EnergyV3.ScaleExponents.crossEnergy (Real.log K) (Real.log L) (Real.log s)) := by
  unfold EnergyV3.ScaleExponents.crossEnergy
  apply min_le_four_exp
  · have h := mul_le_mul_of_nonneg_left (M_le_exp_density hK hL hs) (mul_pos hK hL).le
    rw [Real.exp_add, Real.exp_add, Real.exp_log hK, Real.exp_log hL]
    nlinarith
  · have ha : K ^ 2 * L = Real.exp (2 * Real.log K + Real.log L) := by
      simpa using (exp_linear_pair (a := 2) (b := 1) hK hL).symm
    have hb : s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ) =
        Real.exp (Real.log s + 5 * Real.log K / 2 + Real.log L / 2) := by
      rw [show Real.log s + 5 * Real.log K / 2 + Real.log L / 2 =
        Real.log s + ((5 / 2 : ℝ) * Real.log K + (1 / 2 : ℝ) * Real.log L) by ring,
        Real.exp_add, Real.exp_log hs, exp_linear_pair hK hL]
      ring
    have h := exp_max_le_sum (2 * Real.log K + Real.log L)
      (Real.log s + 5 * Real.log K / 2 + Real.log L / 2)
    have hc := Real.exp_le_exp.mpr (le_max_left (2 * Real.log K + Real.log L)
      (Real.log s + 5 * Real.log K / 2 + Real.log L / 2))
    have hd := Real.exp_le_exp.mpr (le_max_right (2 * Real.log K + Real.log L)
      (Real.log s + 5 * Real.log K / 2 + Real.log L / 2))
    rw [← ha] at hc
    rw [← hb] at hd
    linarith [Real.exp_pos (max (2 * Real.log K + Real.log L)
      (Real.log s + 5 * Real.log K / 2 + Real.log L / 2))]

theorem exp_cross {K L ρ : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp (EnergyV3.ScaleExponents.crossExponent (Real.log K) (Real.log L) ρ) =
      K ^ (2 + 2 * ρ) * L ^ (1 + 2 * ρ) := exp_linear_pair hK hL

theorem cross_ray_scale_bound {K L s ρ : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hslow : 1 / Real.sqrt (K * L) ≤ s)
    (hsup : s ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    min ((K * L) * M K L s) (K ^ 2 * L + s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) *
      (M K L s / s ^ 2) ^ ρ ≤
    16 * ((K * L) ^ (2 + ρ) + K * L ^ (3 + 4 * ρ) +
      K ^ (2 + 2 * ρ) * L ^ (1 + 2 * ρ)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := lt_of_lt_of_le hL0 hLK
  have hs0 := scale_positive hK0 hL0 hslow
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs0.le hsup
  have he := moment_le_exp (M_pos hK0 hL0 hs0) hs0 hρ0 (by linarith : ρ ≤ 1)
    (cross_energy_le_exp hK0 hL0 hs0) (M_le_exp_density hK0 hL0 hs0)
  have hb := EnergyV3.ScaleExponents.cross_ray_bound (Real.log_nonneg hL) hlogs
    (log_scale_lower hK0 hL0 hslow) hρ0 hρ
  have hm := (Real.exp_le_exp.mpr hb).trans
    (exp_max_three_le_sum (rootExponent (Real.log K) (Real.log L) ρ)
      (secondExponent (Real.log K) (Real.log L) ρ)
      (EnergyV3.ScaleExponents.crossExponent (Real.log K) (Real.log L) ρ))
  rw [exp_root hK0 hL0, exp_second hK0 hL0, exp_cross hK0 hL0] at hm
  linarith

theorem full_scale_bound {K L s ρ : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hslow : 1 / Real.sqrt (K * L) ≤ s)
    (hsup : s ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    min ((K * L) * D K L s) (s * (K * L) ^ 2 + K * L ^ 3) *
        (D K L s / s ^ 2) ^ ρ +
      min ((K * L) * M K L s) (K ^ 2 * L + s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) *
        (M K L s / s ^ 2) ^ ρ ≤
    32 * ((K * L) ^ (2 + ρ) + K * L ^ (3 + 4 * ρ) +
      K ^ (2 + 2 * ρ) * L ^ (1 + 2 * ρ) +
      K ^ (1 + 3 * ρ / 2) * L ^ (3 + 5 * ρ / 2)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := lt_of_lt_of_le hL0 hLK
  have hD := same_ray_scale_bound hL hLK hslow hsup hρ0 hρ
  have hM := cross_ray_scale_bound hL hLK hslow hsup hρ0 hρ
  have hp1 : 0 ≤ K * L ^ (3 + 4 * ρ) := by positivity
  have hp2 : 0 ≤ K ^ (2 + 2 * ρ) * L ^ (1 + 2 * ρ) := by positivity
  have hp3 : 0 ≤ K ^ (1 + 3 * ρ / 2) * L ^ (3 + 5 * ρ / 2) := by positivity
  linarith

theorem full_scale_bound_q {K L s q : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hslow : 1 / Real.sqrt (K * L) ≤ s)
    (hsup : s ≤ 1) (hq : 4 ≤ q) (hqu : q ≤ (9 : ℝ) / 2) :
    min ((K * L) * D K L s) (s * (K * L) ^ 2 + K * L ^ 3) *
        (D K L s / s ^ 2) ^ ((q - 4) / 2) +
      min ((K * L) * M K L s) (K ^ 2 * L + s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) *
        (M K L s / s ^ 2) ^ ((q - 4) / 2) ≤
    32 * Arithmetic.fourTerm K L q := by
  have h := full_scale_bound hL hLK hslow hsup
    (ρ := (q - 4) / 2) (by linarith) (by linarith)
  have h1 : 2 + (q - 4) / 2 = q / 2 := by ring
  have h2 : 3 + 4 * ((q - 4) / 2) = 2 * q - 5 := by ring
  have h3 : 2 + 2 * ((q - 4) / 2) = q - 2 := by ring
  have h4 : 1 + 2 * ((q - 4) / 2) = q - 3 := by ring
  have h5 : 1 + 3 * ((q - 4) / 2) / 2 = 3 * q / 4 - 2 := by ring
  have h6 : 3 + 5 * ((q - 4) / 2) / 2 = 5 * q / 4 - 2 := by ring
  simpa only [Arithmetic.fourTerm, h1, h2, h3, h4, h5, h6] using h

end
end CircleDivisor.EnergyV3.ScaleBounds
