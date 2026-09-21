import Mathlib

/-!
# Algebra of the square-root first-spacing range

This file proves the four comparisons in Corollary 1.3 at the level of actual
positive real parameters and real powers.  It does not assume the analytic
first-spacing estimate, either as an axiom or as an external input.
-/

namespace CircleDivisor.FirstSpacingConsequences

noncomputable section

theorem log_monomial_le {K L a b c : ℝ} (hK : 0 < K) (hL : 0 < L)
    (h : a * Real.log K + b * Real.log L ≤ c * (Real.log K + Real.log L)) :
    K ^ a * L ^ b ≤ (K * L) ^ c := by
  apply (Real.log_le_log_iff
    (mul_pos (Real.rpow_pos_of_pos hK a) (Real.rpow_pos_of_pos hL b))
    (Real.rpow_pos_of_pos (mul_pos hK hL) c)).mp
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hK a))
      (ne_of_gt (Real.rpow_pos_of_pos hL b)),
    Real.log_rpow hK, Real.log_rpow hL, Real.log_rpow (mul_pos hK hL),
    Real.log_mul (ne_of_gt hK) (ne_of_gt hL)]
  exact h

theorem spacing_conditions_log {K L q : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hfirst : K ^ (q - 4) ≤ L)
    (hsecond : L ^ (3 * q - 8) ≤ K ^ (8 - q)) :
    (q - 4) * Real.log K ≤ Real.log L ∧
    (3 * q - 8) * Real.log L ≤ (8 - q) * Real.log K := by
  constructor
  · have h := (Real.log_le_log_iff (Real.rpow_pos_of_pos hK (q - 4)) hL).2 hfirst
    rwa [Real.log_rpow hK] at h
  · have h := (Real.log_le_log_iff (Real.rpow_pos_of_pos hL (3 * q - 8))
      (Real.rpow_pos_of_pos hK (8 - q))).2 hsecond
    rwa [Real.log_rpow hK, Real.log_rpow hL] at h

/-- The polynomial comparison explicitly displayed in Corollary 1.3. -/
theorem second_term_polynomial_identity (q : ℝ) :
    (3 * q - 8) * (q - 2) - (3 * q - 10) * (8 - q) = 6 * (q - 4) ^ 2 := by
  ring

theorem second_log_comparison {k l q : ℝ} (hl : 0 ≤ l) (hq : 4 < q)
    (hqu : q ≤ (9 : ℝ) / 2) (hsecond : (3 * q - 8) * l ≤ (8 - q) * k) :
    k + (2 * q - 5) * l ≤ q / 2 * (k + l) := by
  have hq2 : 0 ≤ q - 2 := by linarith
  have hq8 : 0 < 8 - q := by linarith
  have ha := mul_nonneg hq2 (sub_nonneg.mpr hsecond)
  have hb := mul_nonneg (sq_nonneg (q - 4)) hl
  have hc : 0 ≤ (8 - q) * ((q - 2) * k - (3 * q - 10) * l) := by
    nlinarith
  have hd : 0 ≤ (q - 2) * k - (3 * q - 10) * l :=
    nonneg_of_mul_nonneg_right hc hq8
  nlinarith

theorem four_monomial_comparisons {K L q : ℝ} (hL : 1 ≤ L) (hLK : L ≤ K)
    (hq : 4 < q) (hqu : q ≤ (9 : ℝ) / 2)
    (hfirst : K ^ (q - 4) ≤ L)
    (hsecond : L ^ (3 * q - 8) ≤ K ^ (8 - q)) :
    (K * L) ^ (q / 2) ≤ (K * L) ^ (q / 2) ∧
    K * L ^ (2 * q - 5) ≤ (K * L) ^ (q / 2) ∧
    K ^ (q - 2) * L ^ ((q - 1) / 2) ≤ (K * L) ^ (q / 2) ∧
    K ^ (3 * q / 4 - 2) * L ^ (5 * q / 4 - 2) ≤ (K * L) ^ (q / 2) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := lt_of_lt_of_le hL0 hLK
  obtain ⟨hf, hs⟩ := spacing_conditions_log hK0 hL0 hfirst hsecond
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · have hb := second_log_comparison (Real.log_nonneg hL) hq hqu hs
    have hc := log_monomial_le hK0 hL0 (a := 1) (b := 2 * q - 5)
      (c := q / 2) (by simpa using hb)
    simpa using hc
  · apply log_monomial_le hK0 hL0
    nlinarith
  · apply log_monomial_le hK0 hL0
    nlinarith

/-- The bracket in (1.8) is at most four times the square-root moment. -/
theorem four_term_sum_le {K L q : ℝ} (hL : 1 ≤ L) (hLK : L ≤ K)
    (hq : 4 < q) (hqu : q ≤ (9 : ℝ) / 2)
    (hfirst : K ^ (q - 4) ≤ L)
    (hsecond : L ^ (3 * q - 8) ≤ K ^ (8 - q)) :
    (K * L) ^ (q / 2) + K * L ^ (2 * q - 5) +
      K ^ (q - 2) * L ^ ((q - 1) / 2) +
      K ^ (3 * q / 4 - 2) * L ^ (5 * q / 4 - 2) ≤
    4 * (K * L) ^ (q / 2) := by
  obtain ⟨_, h2, h3, h4⟩ := four_monomial_comparisons hL hLK hq hqu hfirst hsecond
  linarith

/-- The region claimed for the endpoint `q = 9/2`, in ordinary real powers. -/
theorem nine_halves_spacing_conditions {K L : ℝ} (hL : 1 ≤ L)
    (hlower : L ^ ((11 : ℝ) / 7) ≤ K) (hupper : K ≤ L ^ (2 : ℕ)) :
    K ^ ((9 : ℝ) / 2 - 4) ≤ L ∧
    L ^ (3 * ((9 : ℝ) / 2) - 8) ≤ K ^ (8 - (9 : ℝ) / 2) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK0 : 0 < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 ((11 : ℝ) / 7)) hlower
  have hlo := (Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 ((11 : ℝ) / 7)) hK0).2 hlower
  rw [Real.log_rpow hL0] at hlo
  have hhi := (Real.log_le_log_iff hK0 (pow_pos hL0 2)).2 hupper
  rw [Real.log_pow] at hhi
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hK0 _) hL0).mp
    rw [Real.log_rpow hK0]
    norm_num at hhi ⊢
    linarith
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _)
      (Real.rpow_pos_of_pos hK0 _)).mp
    rw [Real.log_rpow hL0, Real.log_rpow hK0]
    linarith

theorem nine_halves_four_term_sum {K L : ℝ} (hL : 1 ≤ L)
    (hlower : L ^ ((11 : ℝ) / 7) ≤ K) (hupper : K ≤ L ^ (2 : ℕ)) :
    (K * L) ^ ((9 : ℝ) / 4) + K * L ^ (4 : ℝ) +
      K ^ ((5 : ℝ) / 2) * L ^ ((7 : ℝ) / 4) +
      K ^ ((11 : ℝ) / 8) * L ^ ((29 : ℝ) / 8) ≤
    4 * (K * L) ^ ((9 : ℝ) / 4) := by
  have hLK : L ≤ K := by
    calc
      L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ ((11 : ℝ) / 7) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ K := hlower
  obtain ⟨hf, hs⟩ := nine_halves_spacing_conditions hL hlower hupper
  have h := four_term_sum_le hL hLK (q := (9 : ℝ) / 2) (by norm_num) (by norm_num) hf hs
  norm_num at h ⊢
  exact h

end

end CircleDivisor.FirstSpacingConsequences
