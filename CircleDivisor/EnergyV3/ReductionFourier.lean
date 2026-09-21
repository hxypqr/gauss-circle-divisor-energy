import CircleDivisor.EnergyV3.ReductionWeight
import CircleDivisor.EnergyV3.ReductionDyadic

/-! The complete finite-frequency reduction. The only hypothesis about the
arithmetic exponential sums is the explicit rectangle bound in §6. -/

namespace CircleDivisor.EnergyV3
noncomputable section
open scoped BigOperators

/-- Initial rectangles used by Abel; this is an internal analytic obligation,
not one of the classical external input propositions. -/
def FiniteRectangleBound {ι : Type*} (s : Finset ι) (u : ι → ℝ) (Y : ℕ) (B : ℝ) : Prop :=
  ∀ H : ℕ, 1 ≤ H → H ≤ Y → ∀ n : ℕ, n ≤ H → H + n ≤ Y + 1 →
    ‖∑ i ∈ Finset.range n, frequencySum s u (H + i)‖ ≤ B * H

theorem dyadicBlock_length (Y j : ℕ) (hY : 1 ≤ Y) (hj : j ≤ Nat.log 2 Y) :
    let H := 2 ^ j
    let n := min (2 ^ (j + 1)) (Y + 1) - H
    1 ≤ H ∧ H ≤ Y ∧ 1 ≤ n ∧ n ≤ H ∧ H + n ≤ Y + 1 := by
  dsimp
  have hH : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by omega)
  have hHY := dyadic_block_start_le Y j hY hj
  rw [pow_succ]
  omega

/-- A numerical bound before choosing the cutoff Y, with all actual Vaaler
coefficients, endpoint conventions, and truncated blocks included. -/
theorem finite_fourier_reduction : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} (s : Finset ι) (u : ι → ℝ)
      (hV : ClassicalInputs.VaalerApproximation) (Y : ℕ) (hY : 1 ≤ Y)
      (B : ℝ) (hB : 0 ≤ B), FiniteRectangleBound s u Y B →
      |∑ m ∈ s, Sawtooth.psi (u m)| ≤
        (s.card : ℝ) / (2 * (Y + 1)) +
        C * B * (Nat.log 2 Y + 1) + 2 * B := by
  obtain ⟨W, hW, hWbound, hWlip⟩ := exists_vaalerWeight_bounds
  refine ⟨2 * W / Real.pi, by positivity, ?_⟩
  intro ι s u hV Y hY B hB hrect
  have hmain : ‖∑ h ∈ Finset.Icc 1 Y,
      (vaalerSineCoefficient Y h : ℂ) * frequencySum s u h‖ ≤
      (Nat.log 2 Y + 1) * (B * (2 * W / Real.pi)) := by
    apply norm_sum_le_dyadic_constant
    intro j hj
    obtain ⟨hH, hHY, hn, hnH, hnY⟩ := dyadicBlock_length Y j hY hj
    let H := 2 ^ j
    let n := min (2 ^ (j + 1)) (Y + 1) - H
    rw [dyadicBlock, Finset.sum_Ico_eq_sum_range]
    have hpartial : ∀ k ≤ n,
        ‖∑ i ∈ Finset.range k, frequencySum s u (H + i)‖ ≤ B * H := by
      intro k hk
      exact hrect H hH hHY k (by omega) (by omega)
    have hh := norm_sum_interval_le_abelCost (frequencySum s u)
      (fun h => (vaalerSineCoefficient Y h : ℂ)) H n (B * H)
      ((2 * W / Real.pi) / H) (by positivity) hpartial
      (vaaler_coefficient_abelCost W hW hWbound hWlip Y H n hH hn hnY)
    have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (by omega : H ≠ 0)
    convert hh using 1 <;> field_simp <;> ring
  have herr : ‖∑ h ∈ Finset.Icc 1 Y,
      (fejerCosineCoefficient Y h : ℂ) * frequencySum s u h‖ ≤ 2 * B := by
    have hblock : ∀ j ≤ Nat.log 2 Y,
        ‖∑ h ∈ dyadicBlock Y j,
          (fejerCosineCoefficient Y h : ℂ) * frequencySum s u h‖ ≤
          (B / (Y + 1)) * (2 : ℝ) ^ j := by
      intro j hj
      obtain ⟨hH, hHY, hn, hnH, hnY⟩ := dyadicBlock_length Y j hY hj
      let H := 2 ^ j
      let n := min (2 ^ (j + 1)) (Y + 1) - H
      rw [dyadicBlock, Finset.sum_Ico_eq_sum_range]
      have hpartial : ∀ k ≤ n,
          ‖∑ i ∈ Finset.range k, frequencySum s u (H + i)‖ ≤ B * H := by
        intro k hk
        exact hrect H hH hHY k (by omega) (by omega)
      have hh := norm_sum_interval_le_abelCost (frequencySum s u)
        (fun h => (fejerCosineCoefficient Y h : ℂ)) H n (B * H)
        (1 / (Y + 1)) (by positivity) hpartial
        (fejer_coefficient_abelCost Y H n hH hn hnY)
      convert hh using 1 <;> simp only [H, Nat.cast_pow, Nat.cast_ofNat] <;> ring
    have hh := norm_sum_le_dyadic
      (fun h => (fejerCosineCoefficient Y h : ℂ) * frequencySum s u h)
      Y (fun j => (B / (Y + 1)) * (2 : ℝ) ^ j) hblock
    rw [← Finset.mul_sum] at hh
    apply hh.trans
    calc
      _ ≤ (B / (Y + 1)) * (2 * Y) := mul_le_mul_of_nonneg_left
        (sum_dyadic_starts_le Y hY) (by positivity)
      _ ≤ 2 * B := by
        have hD : 0 < (Y : ℝ) + 1 := by positivity
        rw [div_mul_eq_mul_div, div_le_iff₀ hD]
        nlinarith
  have hfinite := sawtooth_sum_le_fourier s u hV Y hY
  linarith

end
end CircleDivisor.EnergyV3
