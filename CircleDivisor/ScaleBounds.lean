import CircleDivisor.ScaleExponents

/-!
# Uniform numerical bounds at each angular scale

This bridges the logarithmic inequalities of `ScaleExponents` to positive real
parameters and real powers.  The absolute numerical constant is `16`.
-/

namespace CircleDivisor.ScaleBounds

noncomputable section

open ScaleExponents

def D (K L s : ℝ) : ℝ := s * K * L * (1 + 1 / (K * s ^ 2))
def M (K L s : ℝ) : ℝ := D K L s * (1 + 1 / (L * s))

theorem D_expansion {K L s : ℝ} (hK : 0 < K) (hs : 0 < s) :
    D K L s = s * K * L + L / s := by
  dsimp [D]
  field_simp

theorem M_expansion {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    M K L s = s * K * L + K + L / s + 1 / s ^ 2 := by
  dsimp [M]
  rw [D_expansion hK hs]
  field_simp
  ring

theorem D_pos {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    0 < D K L s := by
  dsimp [D]
  positivity

theorem M_pos {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    0 < M K L s := by
  dsimp [M]
  have := D_pos hK hL hs
  positivity

theorem exp_log_triple {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    Real.exp (Real.log s + Real.log K + Real.log L) = s * K * L := by
  rw [Real.exp_add, Real.exp_add, Real.exp_log hs, Real.exp_log hK, Real.exp_log hL]

theorem exp_log_div {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    Real.exp (Real.log L - Real.log s) = L / s := by
  rw [Real.exp_sub, Real.exp_log hL, Real.exp_log hs]

theorem exp_neg_two_log {s : ℝ} (hs : 0 < s) :
    Real.exp (-2 * Real.log s) = 1 / s ^ 2 := by
  rw [show -2 * Real.log s = -(Real.log s + Real.log s) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log hs]
  simp [pow_two, one_div]

theorem D_le_exp_density {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    D K L s ≤ 4 * Real.exp (sameDensity (Real.log K) (Real.log L) (Real.log s)) := by
  have ha := Real.exp_le_exp.mpr (le_max_left
    (Real.log s + Real.log K + Real.log L) (Real.log L - Real.log s))
  have hb := Real.exp_le_exp.mpr (le_max_right
    (Real.log s + Real.log K + Real.log L) (Real.log L - Real.log s))
  rw [exp_log_triple hK hL hs] at ha
  rw [exp_log_div hL hs] at hb
  rw [D_expansion hK hs]
  unfold sameDensity
  linarith [Real.exp_pos (max (Real.log s + Real.log K + Real.log L)
    (Real.log L - Real.log s))]

theorem M_le_exp_density {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    M K L s ≤ 4 * Real.exp (totalDensity (Real.log K) (Real.log L) (Real.log s)) := by
  let a := Real.log s + Real.log K + Real.log L
  let b := Real.log K
  let c := Real.log L - Real.log s
  let d := -2 * Real.log s
  have ha := Real.exp_le_exp.mpr ((le_max_left a b).trans (le_max_left (max a b) (max c d)))
  have hb := Real.exp_le_exp.mpr ((le_max_right a b).trans (le_max_left (max a b) (max c d)))
  have hc := Real.exp_le_exp.mpr ((le_max_left c d).trans (le_max_right (max a b) (max c d)))
  have hd := Real.exp_le_exp.mpr ((le_max_right c d).trans (le_max_right (max a b) (max c d)))
  dsimp [a, b, c, d] at *
  rw [exp_log_triple hK hL hs] at ha
  rw [Real.exp_log hK] at hb
  rw [exp_log_div hL hs] at hc
  rw [exp_neg_two_log hs] at hd
  rw [M_expansion hK hL hs]
  unfold totalDensity
  linarith

theorem min_le_four_exp {A B a b : ℝ}
    (ha : A ≤ 4 * Real.exp a) (hb : B ≤ 4 * Real.exp b) :
    min A B ≤ 4 * Real.exp (min a b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact (min_le_left _ _).trans ha
  · rw [min_eq_right hba]
    exact (min_le_right _ _).trans hb

theorem same_energy_le_exp {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    min ((K * L) * D K L s) (s * (K * L) ^ 2 + K * L ^ 3) ≤
      4 * Real.exp (sameEnergy (Real.log K) (Real.log L) (Real.log s)) := by
  unfold sameEnergy
  apply min_le_four_exp
  · have h := mul_le_mul_of_nonneg_left (D_le_exp_density hK hL hs) (le_of_lt (mul_pos hK hL))
    rw [Real.exp_add, Real.exp_add, Real.exp_log hK, Real.exp_log hL]
    nlinarith
  · have ha : s * (K * L) ^ 2 =
        Real.exp (Real.log s + 2 * (Real.log K + Real.log L)) := by
      rw [show Real.log s + 2 * (Real.log K + Real.log L) =
        Real.log s + (Real.log K + Real.log L) + (Real.log K + Real.log L) by ring]
      simp only [Real.exp_add, Real.exp_log hK, Real.exp_log hL, Real.exp_log hs]
      ring
    have hb : K * L ^ 3 = Real.exp (Real.log K + 3 * Real.log L) := by
      rw [show Real.log K + 3 * Real.log L =
        Real.log K + Real.log L + Real.log L + Real.log L by ring]
      simp only [Real.exp_add, Real.exp_log hK, Real.exp_log hL]
      ring
    have hc := Real.exp_le_exp.mpr (le_max_left
      (Real.log s + 2 * (Real.log K + Real.log L)) (Real.log K + 3 * Real.log L))
    have hd := Real.exp_le_exp.mpr (le_max_right
      (Real.log s + 2 * (Real.log K + Real.log L)) (Real.log K + 3 * Real.log L))
    rw [← ha] at hc
    rw [← hb] at hd
    linarith [Real.exp_pos (max (Real.log s + 2 * (Real.log K + Real.log L))
      (Real.log K + 3 * Real.log L))]

theorem cross_energy_le_exp {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    min ((K * L) * M K L s) ((K * L) * s ^ 2 * K ^ 2 * L) ≤
      4 * Real.exp (crossEnergy (Real.log K) (Real.log L) (Real.log s)) := by
  unfold crossEnergy
  apply min_le_four_exp
  · have h := mul_le_mul_of_nonneg_left (M_le_exp_density hK hL hs) (le_of_lt (mul_pos hK hL))
    rw [Real.exp_add, Real.exp_add, Real.exp_log hK, Real.exp_log hL]
    nlinarith
  · have he : Real.exp (Real.log K + Real.log L + 2 * Real.log s +
        2 * Real.log K + Real.log L) = (K * L) * s ^ 2 * K ^ 2 * L := by
      rw [show Real.log K + Real.log L + 2 * Real.log s + 2 * Real.log K + Real.log L =
        Real.log K + Real.log L + Real.log s + Real.log s +
        Real.log K + Real.log K + Real.log L by ring]
      simp only [Real.exp_add, Real.exp_log hK, Real.exp_log hL, Real.exp_log hs]
      ring
    rw [he]
    have hp : 0 ≤ (K * L) * s ^ 2 * K ^ 2 * L := by positivity
    linarith

theorem amplitude_power_le_exp {A d s ρ : ℝ} (hA : 0 < A) (hs : 0 < s)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hbound : A ≤ 4 * Real.exp d) :
    (A / s ^ 2) ^ ρ ≤ 4 * Real.exp (ρ * (d - 2 * Real.log s)) := by
  have he : Real.exp (d - 2 * Real.log s) = Real.exp d / s ^ 2 := by
    rw [sub_eq_add_neg, Real.exp_add, show -(2 * Real.log s) = -2 * Real.log s by ring,
      exp_neg_two_log hs]
    ring
  have hab : A / s ^ 2 ≤ 4 * Real.exp (d - 2 * Real.log s) := by
    rw [he]
    calc
      A / s ^ 2 ≤ (4 * Real.exp d) / s ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hs)).2 hbound
      _ = 4 * (Real.exp d / s ^ 2) := by ring
  have hr := Real.rpow_le_rpow (show 0 ≤ A / s ^ 2 by positivity) hab hρ0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt (Real.exp_pos _)),
    ← Real.exp_mul] at hr
  have hc : (4 : ℝ) ^ ρ ≤ 4 := by
    calc
      (4 : ℝ) ^ ρ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ1
      _ = 4 := Real.rpow_one _
  have hm := mul_le_mul_of_nonneg_right hc (le_of_lt (Real.exp_pos ((d - 2 * Real.log s) * ρ)))
  have hz := hr.trans hm
  simpa only [mul_comm ρ] using hz

theorem moment_le_exp {A B e d s ρ : ℝ} (hB : 0 < B) (hs : 0 < s)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (henergy : A ≤ 4 * Real.exp e) (hdensity : B ≤ 4 * Real.exp d) :
    A * (B / s ^ 2) ^ ρ ≤ 16 * Real.exp (e + ρ * (d - 2 * Real.log s)) := by
  have hp := amplitude_power_le_exp hB hs hρ0 hρ1 hdensity
  calc
    A * (B / s ^ 2) ^ ρ ≤ (4 * Real.exp e) * (4 * Real.exp (ρ * (d - 2 * Real.log s))) :=
      mul_le_mul henergy hp (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = 16 * Real.exp (e + ρ * (d - 2 * Real.log s)) := by
      rw [Real.exp_add]
      ring

theorem exp_max_le_sum (a b : ℝ) : Real.exp (max a b) ≤ Real.exp a + Real.exp b := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    linarith [Real.exp_pos a]
  · rw [max_eq_left hba]
    linarith [Real.exp_pos b]

theorem exp_max_three_le_sum (a b c : ℝ) :
    Real.exp (max a (max b c)) ≤ Real.exp a + Real.exp b + Real.exp c := by
  have h1 := exp_max_le_sum a (max b c)
  have h2 := exp_max_le_sum b c
  linarith

theorem exp_root {K L ρ : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp (rootExponent (Real.log K) (Real.log L) ρ) = (K * L) ^ (2 + ρ) := by
  rw [Real.rpow_def_of_pos (mul_pos hK hL), Real.log_mul (ne_of_gt hK) (ne_of_gt hL)]
  unfold rootExponent
  congr 1
  ring

theorem exp_linear_pair {K L a b : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp (a * Real.log K + b * Real.log L) = K ^ a * L ^ b := by
  rw [Real.exp_add, Real.rpow_def_of_pos hK, Real.rpow_def_of_pos hL]
  congr 2 <;> ring

theorem exp_radial {K L ρ : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp (radialExponent (Real.log K) (Real.log L) ρ) =
      K ^ (1 + 3 * ρ / 2) * L ^ (3 + 5 * ρ / 2) := exp_linear_pair hK hL

theorem exp_cross {K L ρ : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp (crossExponent (Real.log K) (Real.log L) ρ) =
      K ^ (2 + 2 * ρ) * L ^ (3 / 2 + ρ) := exp_linear_pair hK hL

theorem exp_second {K L ρ : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp (secondExponent (Real.log K) (Real.log L) ρ) = K * L ^ (3 + 4 * ρ) := by
  unfold secondExponent
  rw [Real.exp_add, Real.exp_log hK, Real.rpow_def_of_pos hL]
  congr 2
  ring

theorem scale_positive {K L s : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hslow : 1 / Real.sqrt (K * L) ≤ s) : 0 < s :=
  lt_of_lt_of_le (one_div_pos.mpr (Real.sqrt_pos.mpr (mul_pos hK hL))) hslow

theorem log_scale_lower {K L s : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hslow : 1 / Real.sqrt (K * L) ≤ s) :
    -(Real.log K + Real.log L) / 2 ≤ Real.log s := by
  have hs := scale_positive hK hL hslow
  have hroot := Real.sqrt_pos.mpr (mul_pos hK hL)
  have hlog := (Real.log_le_log_iff (one_div_pos.mpr hroot) hs).2 hslow
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hroot),
    Real.log_one, Real.log_sqrt (le_of_lt (mul_pos hK hL)),
    Real.log_mul (ne_of_gt hK) (ne_of_gt hL)] at hlog
  linarith

/-- The numerical same-ray estimate, uniformly over every permitted angular scale. -/
theorem same_ray_scale_bound {K L s ρ : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hslow : 1 / Real.sqrt (K * L) ≤ s)
    (hsup : s ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    min ((K * L) * D K L s) (s * (K * L) ^ 2 + K * L ^ 3) *
      (D K L s / s ^ 2) ^ ρ ≤
    16 * ((K * L) ^ (2 + ρ) + K ^ (1 + 3 * ρ / 2) * L ^ (3 + 5 * ρ / 2)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := lt_of_lt_of_le hL0 hLK
  have hs0 := scale_positive hK0 hL0 hslow
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos (le_of_lt hs0) hsup
  have he := moment_le_exp (D_pos hK0 hL0 hs0) hs0 hρ0 (by linarith : ρ ≤ 1)
    (same_energy_le_exp hK0 hL0 hs0) (D_le_exp_density hK0 hL0 hs0)
  have hb := ScaleExponents.same_ray_bound (Real.log_nonneg (hL.trans hLK)) hlogs
    (log_scale_lower hK0 hL0 hslow) hρ0 hρ
  have hm := (Real.exp_le_exp.mpr hb).trans
    (exp_max_le_sum (rootExponent (Real.log K) (Real.log L) ρ)
      (radialExponent (Real.log K) (Real.log L) ρ))
  rw [exp_root hK0 hL0, exp_radial hK0 hL0] at hm
  linarith

/-- The numerical cross-ray estimate, including the crossing scale. -/
theorem cross_ray_scale_bound {K L s ρ : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hslow : 1 / Real.sqrt (K * L) ≤ s)
    (hsup : s ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    min ((K * L) * M K L s) ((K * L) * s ^ 2 * K ^ 2 * L) *
      (M K L s / s ^ 2) ^ ρ ≤
    16 * ((K * L) ^ (2 + ρ) + K * L ^ (3 + 4 * ρ) +
      K ^ (2 + 2 * ρ) * L ^ (3 / 2 + ρ)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := lt_of_lt_of_le hL0 hLK
  have hs0 := scale_positive hK0 hL0 hslow
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos (le_of_lt hs0) hsup
  have he := moment_le_exp (M_pos hK0 hL0 hs0) hs0 hρ0 (by linarith : ρ ≤ 1)
    (cross_energy_le_exp hK0 hL0 hs0) (M_le_exp_density hK0 hL0 hs0)
  have hb := ScaleExponents.cross_ray_bound (k := Real.log K) (Real.log_nonneg hL) hlogs hρ0 hρ
  have hm := (Real.exp_le_exp.mpr hb).trans
    (exp_max_three_le_sum (rootExponent (Real.log K) (Real.log L) ρ)
      (secondExponent (Real.log K) (Real.log L) ρ)
      (crossExponent (Real.log K) (Real.log L) ρ))
  rw [exp_root hK0 hL0, exp_second hK0 hL0, exp_cross hK0 hL0] at hm
  linarith

/-- Adding the two separately controlled amplitudes gives the four moment monomials. -/
theorem full_scale_bound {K L s ρ : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hslow : 1 / Real.sqrt (K * L) ≤ s)
    (hsup : s ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) :
    min ((K * L) * D K L s) (s * (K * L) ^ 2 + K * L ^ 3) *
        (D K L s / s ^ 2) ^ ρ +
      min ((K * L) * M K L s) ((K * L) * s ^ 2 * K ^ 2 * L) *
        (M K L s / s ^ 2) ^ ρ ≤
    32 * ((K * L) ^ (2 + ρ) + K * L ^ (3 + 4 * ρ) +
      K ^ (2 + 2 * ρ) * L ^ (3 / 2 + ρ) +
      K ^ (1 + 3 * ρ / 2) * L ^ (3 + 5 * ρ / 2)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := lt_of_lt_of_le hL0 hLK
  have hD := same_ray_scale_bound hL hLK hslow hsup hρ0 hρ
  have hM := cross_ray_scale_bound hL hLK hslow hsup hρ0 hρ
  have hp1 : 0 ≤ K * L ^ (3 + 4 * ρ) := by positivity
  have hp2 : 0 ≤ K ^ (2 + 2 * ρ) * L ^ (3 / 2 + ρ) := by positivity
  have hp3 : 0 ≤ K ^ (1 + 3 * ρ / 2) * L ^ (3 + 5 * ρ / 2) := by positivity
  linarith

/-- The same result written in the moment parameter `q`, matching (1.8). -/
theorem full_scale_bound_q {K L s q : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hslow : 1 / Real.sqrt (K * L) ≤ s)
    (hsup : s ≤ 1) (hq : 4 ≤ q) (hqu : q ≤ (9 : ℝ) / 2) :
    min ((K * L) * D K L s) (s * (K * L) ^ 2 + K * L ^ 3) *
        (D K L s / s ^ 2) ^ ((q - 4) / 2) +
      min ((K * L) * M K L s) ((K * L) * s ^ 2 * K ^ 2 * L) *
        (M K L s / s ^ 2) ^ ((q - 4) / 2) ≤
    32 * ((K * L) ^ (q / 2) + K * L ^ (2 * q - 5) +
      K ^ (q - 2) * L ^ ((q - 1) / 2) +
      K ^ (3 * q / 4 - 2) * L ^ (5 * q / 4 - 2)) := by
  have h := full_scale_bound hL hLK hslow hsup
    (ρ := (q - 4) / 2) (by linarith) (by linarith)
  have h1 : 2 + (q - 4) / 2 = q / 2 := by ring
  have h2 : 3 + 4 * ((q - 4) / 2) = 2 * q - 5 := by ring
  have h3 : 2 + 2 * ((q - 4) / 2) = q - 2 := by ring
  have h4 : 3 / 2 + (q - 4) / 2 = (q - 1) / 2 := by ring
  have h5 : 1 + 3 * ((q - 4) / 2) / 2 = 3 * q / 4 - 2 := by ring
  have h6 : 3 + 5 * ((q - 4) / 2) / 2 = 5 * q / 4 - 2 := by ring
  rwa [h1, h2, h3, h4, h5, h6] at h

end

end CircleDivisor.ScaleBounds
