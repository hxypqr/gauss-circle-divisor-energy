import CircleDivisor.ClassicalInputs
import Mathlib.Algebra.BigOperators.Module

/-! Exact finite Abel summation and the finite Vaaler sum. All bounds here refer
to the actual coefficients and actual exponential sums. -/

namespace CircleDivisor.EnergyV3
noncomputable section
open scoped BigOperators

/-- The total discrete variation, including the final endpoint term. -/
def abelCost (b : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖b (n - 1)‖ + ∑ i ∈ Finset.range (n - 1), ‖b (i + 1) - b i‖

/-- Discrete Abel's lemma, with exactly the initial partial sums that occur in
the manuscript's rectangle estimate. -/
theorem norm_sum_mul_le_abelCost (A b : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, A i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, b i * A i‖ ≤ B * abelCost b n := by
  have hformula := Finset.sum_range_by_parts b A n
  simp only [smul_eq_mul] at hformula
  rw [hformula]
  calc
    _ ≤ ‖b (n - 1) * ∑ i ∈ Finset.range n, A i‖ +
        ‖∑ i ∈ Finset.range (n - 1), (b (i + 1) - b i) *
          ∑ j ∈ Finset.range (i + 1), A j‖ := norm_sub_le _ _
    _ ≤ ‖b (n - 1)‖ * B +
        ∑ i ∈ Finset.range (n - 1), ‖b (i + 1) - b i‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left (hpartial (i + 1) (by
          have := Finset.mem_range.mp hi
          omega)) (norm_nonneg _)
    _ = B * abelCost b n := by rw [← Finset.sum_mul]; unfold abelCost; ring

/-- Translated intervals, including a truncated final block. -/
theorem norm_sum_interval_le_abelCost (A b : ℕ → ℂ) (H n : ℕ) (B V : ℝ)
    (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, A (H + i)‖ ≤ B)
    (hcost : abelCost (fun i => b (H + i)) n ≤ V) :
    ‖∑ i ∈ Finset.range n, b (H + i) * A (H + i)‖ ≤ B * V :=
  (norm_sum_mul_le_abelCost (fun i => A (H + i)) (fun i => b (H + i)) n B
    hB hpartial).trans (mul_le_mul_of_nonneg_left hcost hB)

theorem abelCost_mul (b c : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) (B C : ℝ)
    (hb : ∀ i < n, ‖b i‖ ≤ B) (hc : ∀ i < n, ‖c i‖ ≤ C) :
    abelCost (fun i => b i * c i) n ≤ B * abelCost c n +
      C * ∑ i ∈ Finset.range (n - 1), ‖b (i + 1) - b i‖ := by
  unfold abelCost
  calc
    _ ≤ B * ‖c (n - 1)‖ + ∑ i ∈ Finset.range (n - 1),
        (C * ‖b (i + 1) - b i‖ + B * ‖c (i + 1) - c i‖) := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb (n - 1) (by omega)) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have heq : b (i + 1) * c (i + 1) - b i * c i =
            (b (i + 1) - b i) * c (i + 1) + b i * (c (i + 1) - c i) := by ring
        rw [heq]
        apply (norm_add_le _ _).trans
        simp only [norm_mul]
        apply add_le_add
        · simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left (hc (i + 1) (by omega))
              (norm_nonneg (b (i + 1) - b i))
        · exact mul_le_mul_of_nonneg_right (hb i (by omega)) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

theorem abelCost_real_antitone (b : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hb : ∀ i < n, 0 ≤ b i) (hmono : ∀ i < n - 1, b (i + 1) ≤ b i) :
    abelCost (fun i => (b i : ℂ)) n = b 0 := by
  have hsum : ∀ k ≤ n - 1, ∑ i ∈ Finset.range k, (b i - b (i + 1)) = b 0 - b k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih (by omega)]; ring
  unfold abelCost
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb (n - 1) (by omega))]
  have hd : ∑ i ∈ Finset.range (n - 1), ‖(b (i + 1) : ℂ) - b i‖ =
      ∑ i ∈ Finset.range (n - 1), (b i - b (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hmono i (Finset.mem_range.mp hi)))]
    ring
  rw [hd, hsum (n - 1) le_rfl]
  ring

def vaalerSineCoefficient (Y h : ℕ) : ℝ :=
  ClassicalInputs.vaalerWeight ((h : ℝ) / (Y + 1)) / (Real.pi * h)

def fejerCosineCoefficient (Y h : ℕ) : ℝ :=
  (1 - (h : ℝ) / (Y + 1)) / (Y + 1)

theorem exponential_re (t : ℝ) : (exponential t).re = Real.cos (2 * Real.pi * t) := by
  simp [exponential, Complex.exp_re]

theorem exponential_im (t : ℝ) : (exponential t).im = Real.sin (2 * Real.pi * t) := by
  simp [exponential, Complex.exp_im]

def frequencySum {ι : Type*} (s : Finset ι) (u : ι → ℝ) (h : ℕ) : ℂ :=
  ∑ m ∈ s, exponential ((h : ℝ) * u m)

theorem vaaler_sum_eq_im {ι : Type*} (s : Finset ι) (u : ι → ℝ) (Y : ℕ) :
    ∑ m ∈ s, ClassicalInputs.vaalerApproximation Y (u m) =
      -(∑ h ∈ Finset.Icc 1 Y,
        (vaalerSineCoefficient Y h : ℂ) * frequencySum s u h).im := by
  simp only [ClassicalInputs.vaalerApproximation, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, frequencySum, Complex.im_sum,
    exponential_im, Finset.mul_sum, vaalerSineCoefficient]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro m hm
  congr 1 <;> ring

theorem fejer_sum_eq_re {ι : Type*} (s : Finset ι) (u : ι → ℝ) (Y : ℕ) :
    ∑ m ∈ s, ClassicalInputs.fejerRemainder Y (u m) =
      (s.card : ℝ) / (2 * (Y + 1)) +
      (∑ h ∈ Finset.Icc 1 Y,
        (fejerCosineCoefficient Y h : ℂ) * frequencySum s u h).re := by
  simp only [ClassicalInputs.fejerRemainder, add_div, Finset.sum_add_distrib]
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, frequencySum, Complex.re_sum,
    exponential_re, Finset.mul_sum, fejerCosineCoefficient]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  · field_simp
    <;> ring
  · apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro m hm
    congr 1 <;> ring

/-- Finite Vaaler assembly preserving cancellation inside each frequency sum.
In particular, it never replaces the frequency sum by the sum of its norms. -/
theorem sawtooth_sum_le_fourier {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hV : ClassicalInputs.VaalerApproximation) (Y : ℕ) (hY : 1 ≤ Y) :
    |∑ m ∈ s, Sawtooth.psi (u m)| ≤ (s.card : ℝ) / (2 * (Y + 1)) +
      ‖∑ h ∈ Finset.Icc 1 Y,
        (vaalerSineCoefficient Y h : ℂ) * frequencySum s u h‖ +
      ‖∑ h ∈ Finset.Icc 1 Y,
        (fejerCosineCoefficient Y h : ℂ) * frequencySum s u h‖ := by
  have hdiff : |∑ m ∈ s, (Sawtooth.psi (u m) -
      ClassicalInputs.vaalerApproximation Y (u m))| ≤
      ∑ m ∈ s, ClassicalInputs.fejerRemainder Y (u m) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun m hm => hV Y hY (u m))
  rw [Finset.sum_sub_distrib, vaaler_sum_eq_im, fejer_sum_eq_re] at hdiff
  have htri := abs_sub (∑ m ∈ s, Sawtooth.psi (u m))
    (-(∑ h ∈ Finset.Icc 1 Y,
      (vaalerSineCoefficient Y h : ℂ) * frequencySum s u h).im)
  have hmain := Complex.abs_im_le_norm (∑ h ∈ Finset.Icc 1 Y,
      (vaalerSineCoefficient Y h : ℂ) * frequencySum s u h)
  have herr := Complex.re_le_norm (∑ h ∈ Finset.Icc 1 Y,
      (fejerCosineCoefficient Y h : ℂ) * frequencySum s u h)
  have htri' := abs_add_le
    ((∑ m ∈ s, Sawtooth.psi (u m)) -
      (-(∑ h ∈ Finset.Icc 1 Y,
        (vaalerSineCoefficient Y h : ℂ) * frequencySum s u h).im))
    (-(∑ h ∈ Finset.Icc 1 Y,
        (vaalerSineCoefficient Y h : ℂ) * frequencySum s u h).im)
  rw [sub_add_cancel, abs_neg] at htri'
  linarith

end
end CircleDivisor.EnergyV3
