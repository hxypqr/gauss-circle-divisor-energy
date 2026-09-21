import CircleDivisor.EnergyV3.AmplitudeCountable

/-! The numerical assembly of the amplitude integration: cutoffs, the actual
dyadic scale range, and absorption of the number of scales. -/

namespace CircleDivisor.EnergyV3.AmplitudeScale
noncomputable section
open MeasureTheory GuthMaldague AmplitudeCountable
open scoped BigOperators ENNReal

theorem cutoff_power {B A d s q : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hd : 0 ≤ d) (hs : 0 < s) :
    cutoff B (A * d) s ^ (q - 4) =
      (2 * B * A) ^ ((q - 4) / 2) * (d / s ^ 2) ^ ((q - 4) / 2) := by
  have hc : cutoff B (A * d) s ^ (2 : ℕ) = (2 * B * A) * (d / s ^ 2) := by
    unfold cutoff
    rw [div_pow, Real.sq_sqrt (by positivity)]
    ring
  calc
    _ = (cutoff B (A * d) s ^ (2 : ℕ)) ^ ((q - 4) / 2) := by
      rw [← Real.rpow_natCast_mul (cutoff_nonneg hs.le)]
      congr 1
      push_cast
      ring
    _ = _ := by rw [hc, Real.mul_rpow (by positivity) (by positivity)]

theorem scale_range {P : ℝ} {n j : ℕ} (hP : 1 ≤ P)
    (hR : radius n < 4 * P) (hj : j ∈ Finset.Ioo 0 n) :
    1 / Real.sqrt P ≤ scale j ∧ scale j ≤ 1 := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hjn : j + 1 ≤ n := by simpa using (Finset.mem_Ioo.mp hj).2
  have hp : (4 : ℝ) ^ (j + 1) ≤ (4 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hjn
  have hp2 : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hsq : ((2 : ℝ) ^ j) ^ 2 ≤ P := by
    rw [pow_succ] at hp
    unfold radius at hR
    nlinarith [hp2]
  have hroot : (2 : ℝ) ^ j ≤ Real.sqrt P := by
    nlinarith [Real.sq_sqrt hP0.le, Real.sqrt_nonneg P, pow_pos (by norm_num : (0 : ℝ) < 2) j]
  refine ⟨?_, ?_⟩
  · simpa [scale, one_div] using one_div_le_one_div_of_le (pow_pos (by norm_num) j) hroot
  · unfold scale
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem scale_count {P τ : ℝ} {n : ℕ} (hP : 1 ≤ P)
    (hR : radius n < 4 * P) (hτ : 0 < τ) :
    ((Finset.Ioo 0 n).card : ℝ) ≤ (1 / (τ * Real.log 4) + 1) * P ^ τ := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hr := Real.log_le_log (radius_pos n) hR.le
  rw [radius, Real.log_pow, Real.log_mul (by norm_num) hP0.ne'] at hr
  have hl := Real.log_le_rpow_div hP0.le hτ
  have hn : (n : ℝ) ≤ P ^ τ / (τ * Real.log 4) + 1 := by
    have hh : (n : ℝ) - 1 ≤ P ^ τ / (τ * Real.log 4) := by
      rw [le_div_iff₀ (mul_pos hτ hlog4)]
      have hh : ((n : ℝ) - 1) * Real.log 4 ≤ P ^ τ / τ := by linarith
      have ht := (le_div_iff₀ hτ).mp hh
      nlinarith
    linarith
  have hcard : ((Finset.Ioo 0 n).card : ℝ) ≤ n := by
    exact_mod_cast (show (Finset.Ioo 0 n).card ≤ n by simp)
  have hone : 1 ≤ P ^ τ := Real.one_le_rpow hP hτ.le
  calc
    _ ≤ P ^ τ / (τ * Real.log 4) + 1 := hcard.trans hn
    _ ≤ P ^ τ / (τ * Real.log 4) + P ^ τ := by linarith
    _ = _ := by ring

/-- A dyadic radius with the strict upper inequality needed for the finest
nonterminal scale. Exact powers are handled without rounding up twice. -/
theorem exists_radius {P : ℝ} (hP : 1 ≤ P) : ∃ n : ℕ, P ≤ radius n ∧ radius n < 4 * P := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hP (by norm_num : (1 : ℝ) < 4)
  by_cases he : P = (4 : ℝ) ^ n
  · refine ⟨n, ?_, ?_⟩ <;> simp only [radius, he]
    · exact le_rfl
    · nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) n]
  · refine ⟨n + 1, hn'.le, ?_⟩
    have hlt : (4 : ℝ) ^ n < P := lt_of_le_of_ne hn (Ne.symm he)
    dsimp [radius]
    rw [pow_succ]
    nlinarith

def sameProfile (K L s : ℝ) : ℝ :=
  min ((K * L) * CircleDivisor.ScaleBounds.D K L s) (s * (K * L) ^ 2 + K * L ^ 3)

def crossProfile (K L s : ℝ) : ℝ :=
  min ((K * L) * CircleDivisor.ScaleBounds.M K L s)
    (K ^ 2 * L + s * K ^ (5 / 2 : ℝ) * L ^ (1 / 2 : ℝ))

theorem profile_nonneg {K L s : ℝ} (hK : 0 < K) (hL : 0 < L) (hs : 0 < s) :
    0 ≤ sameProfile K L s ∧ 0 ≤ crossProfile K L s := by
  have hd := (CircleDivisor.ScaleBounds.D_pos hK hL hs).le
  have hm := (CircleDivisor.ScaleBounds.M_pos hK hL hs).le
  constructor <;> dsimp only [sameProfile, crossProfile] <;> positivity

theorem scale_term {K L s q B A E : ℝ} (hL : 1 ≤ L) (hLK : L ≤ K)
    (hslow : 1 / Real.sqrt (K * L) ≤ s) (hsup : s ≤ 1)
    (hq : 4 ≤ q) (hqu : q ≤ (9 : ℝ) / 2) (hB : 0 ≤ B) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    (E * sameProfile K L s) * cutoff B (A * CircleDivisor.ScaleBounds.D K L s) s ^ (q - 4) +
      (E * crossProfile K L s) * cutoff B (A * CircleDivisor.ScaleBounds.M K L s) s ^ (q - 4) ≤
      32 * E * (2 * B * A) ^ ((q - 4) / 2) * Arithmetic.fourTerm K L q := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := hL0.trans_le hLK
  have hs := CircleDivisor.ScaleBounds.scale_positive hK0 hL0 hslow
  rw [cutoff_power hB hA (CircleDivisor.ScaleBounds.D_pos hK0 hL0 hs).le hs,
    cutoff_power hB hA (CircleDivisor.ScaleBounds.M_pos hK0 hL0 hs).le hs]
  have hh := mul_le_mul_of_nonneg_left (ScaleBounds.full_scale_bound_q hL hLK hslow hsup hq hqu)
    (show 0 ≤ E * (2 * B * A) ^ ((q - 4) / 2) by positivity)
  dsimp [sameProfile, crossProfile]
  nlinarith only [hh]

theorem scale_sum {K L q B A E : ℝ} {n : ℕ} (hL : 1 ≤ L) (hLK : L ≤ K)
    (hR : radius n < 4 * (K * L)) (hq : 4 ≤ q) (hqu : q ≤ (9 : ℝ) / 2)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    (∑ j ∈ Finset.Ioo 0 n,
      ((E * sameProfile K L (scale j)) *
          cutoff B (A * CircleDivisor.ScaleBounds.D K L (scale j)) (scale j) ^ (q - 4) +
       (E * crossProfile K L (scale j)) *
          cutoff B (A * CircleDivisor.ScaleBounds.M K L (scale j)) (scale j) ^ (q - 4))) ≤
      32 * E * (2 * B * A) ^ ((q - 4) / 2) * Arithmetic.fourTerm K L q *
        ((Finset.Ioo 0 n).card : ℝ) := by
  have hP : 1 ≤ K * L := one_le_mul_of_one_le_of_one_le (hL.trans hLK) hL
  calc
    _ ≤ ∑ _j ∈ Finset.Ioo 0 n,
        32 * E * (2 * B * A) ^ ((q - 4) / 2) * Arithmetic.fourTerm K L q := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hl, hu⟩ := scale_range hP hR hj
      exact scale_term hL hLK hl hu hq hqu hB hA hE
    _ = _ := by simp [mul_comm]

end
end CircleDivisor.EnergyV3.AmplitudeScale
