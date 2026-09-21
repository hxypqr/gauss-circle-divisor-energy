import CircleDivisor.EnergyV3.KernelDerivatives
import CircleDivisor.FourierLocalization

namespace CircleDivisor.EnergyV3.KernelBounds
noncomputable section
open GuthMaldague KernelDerivatives MeasureTheory
open scoped BigOperators ContDiff FourierTransform
set_option maxHeartbeats 1200000

def schwartzAffine (f : SchwartzMap Space ℂ) (L : Space →L[ℝ] Space) (c : Space) : Space → ℂ :=
  fun u => f (c + L u)

theorem schwartzAffine_smooth (f : SchwartzMap Space ℂ) (L : Space →L[ℝ] Space) (c : Space) :
    ContDiff ℝ ∞ (schwartzAffine f L c) :=
  f.smooth'.comp (contDiff_const.add L.contDiff)

theorem schwartzAffine_derivative_bound (f : SchwartzMap Space ℂ) (L : Space →L[ℝ] Space)
    (c : Space) (C : ℝ) (hC : 0 ≤ C) (hL : ‖L‖ ≤ C) (n : ℕ) (u : Space) :
    ‖iteratedFDeriv ℝ n (schwartzAffine f L c) u‖ ≤
      SchwartzMap.seminorm ℝ 0 n f * C ^ n := by
  let g : Space → ℂ := fun v => f (c + v)
  have hg : ContDiff ℝ ∞ g := f.smooth'.comp (contDiff_const.add contDiff_id)
  have heq : schwartzAffine f L c = g ∘ L := rfl
  rw [heq, L.iteratedFDeriv_comp_right hg u (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hseminorm : ‖iteratedFDeriv ℝ n g (L u)‖ ≤ SchwartzMap.seminorm ℝ 0 n f := by
    dsimp only [g]
    rw [iteratedFDeriv_comp_add_left]
    simpa using f.le_seminorm ℝ 0 n (c + L u)
  exact mul_le_mul hseminorm (pow_le_pow_left₀ (norm_nonneg L) hL n)
    (pow_nonneg (norm_nonneg L) n) (by positivity)

def normalizedKernel (f : SchwartzMap Space ℂ) (L : Space →L[ℝ] Space) (c : Space) : Space → ℂ :=
  fun u => schwartzAffine f L c u * (baseWeight u : ℂ)

theorem normalizedKernel_smooth (f : SchwartzMap Space ℂ) (L : Space →L[ℝ] Space) (c : Space) :
    ContDiff ℝ ∞ (normalizedKernel f L c) :=
  (schwartzAffine_smooth f L c).mul baseWeight_complex_smooth

def kernelDerivativeConstant (f : SchwartzMap Space ℂ) (C : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ 0 i f * C ^ i) * baseDerivativeConstant (n - i)

theorem kernelDerivativeConstant_nonneg (f : SchwartzMap Space ℂ) (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ kernelDerivativeConstant f C n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (baseDerivativeConstant_nonneg _)

theorem normalizedKernel_derivative_bound (f : SchwartzMap Space ℂ) (L : Space →L[ℝ] Space)
    (c : Space) (C : ℝ) (hC : 0 ≤ C) (hL : ‖L‖ ≤ C) (n : ℕ) (u : Space) :
    ‖iteratedFDeriv ℝ n (normalizedKernel f L c) u‖ ≤
      kernelDerivativeConstant f C n * baseWeight u := by
  unfold normalizedKernel
  apply (norm_iteratedFDeriv_mul_le (schwartzAffine_smooth f L c) baseWeight_complex_smooth
    u (n := n) (by exact_mod_cast le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℝ 0 i f * C ^ i) *
          (baseDerivativeConstant (n - i) * baseWeight u) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (schwartzAffine_derivative_bound f L c C hC hL i u)
          (Nat.cast_nonneg _)
      · exact baseWeight_derivative_bound (n - i) u
      · positivity
      · positivity
    _ = kernelDerivativeConstant f C n * baseWeight u := by
      unfold kernelDerivativeConstant
      simp_rw [← mul_assoc]
      rw [Finset.sum_mul]

theorem normalizedKernel_derivative_integrable (f : SchwartzMap Space ℂ)
    (L : Space →L[ℝ] Space) (c : Space) (n : ℕ) :
    Integrable (fun u => ‖iteratedFDeriv ℝ n (normalizedKernel f L c) u‖) := by
  have hmajorant := baseWeight_integrable.const_mul (kernelDerivativeConstant f ‖L‖ n)
  apply hmajorant.mono'
  · exact ((normalizedKernel_smooth f L c).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).norm.aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact normalizedKernel_derivative_bound f L c ‖L‖ (norm_nonneg _) le_rfl n u

theorem normalizedKernel_derivative_integral_bound (f : SchwartzMap Space ℂ)
    (L : Space →L[ℝ] Space) (c : Space) (C : ℝ) (hC : 0 ≤ C) (hL : ‖L‖ ≤ C) (n : ℕ) :
    (∫ u, ‖iteratedFDeriv ℝ n (normalizedKernel f L c) u‖) ≤
      kernelDerivativeConstant f C n * weightNormalization := by
  change _ ≤ kernelDerivativeConstant f C n * ∫ u : Space, baseWeight u
  rw [← integral_const_mul]
  apply integral_mono (normalizedKernel_derivative_integrable f L c n)
    (baseWeight_integrable.const_mul _)
  exact normalizedKernel_derivative_bound f L c C hC hL n

theorem normalizedKernel_fourier_poly_bound (f : SchwartzMap Space ℂ)
    (L : Space →L[ℝ] Space) (c : Space) (C : ℝ) (hC : 0 ≤ C) (hL : ‖L‖ ≤ C)
    (n : ℕ) (η : Space) :
    ‖η‖ ^ n * ‖𝓕 (normalizedKernel f L c) η‖ ≤
      2 ^ n * ∑ j ∈ Finset.range (n + 1), kernelDerivativeConstant f C j * weightNormalization := by
  have hi : ∀ k j : ℕ, (k : ℕ∞) ≤ 0 → (j : ℕ∞) ≤ ⊤ →
      Integrable (fun u => ‖u‖ ^ k * ‖iteratedFDeriv ℝ j (normalizedKernel f L c) u‖) := by
    intro k j hk hj
    have hk0 : k = 0 := by exact_mod_cast (le_zero_iff.mp hk)
    subst k
    simpa using normalizedKernel_derivative_integrable f L c j
  have hh := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (normalizedKernel_smooth f L c) hi (k := 0) (n := n)
    (by norm_num : (0 : ℕ∞) ≤ 0) (by simp) η
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
    Finset.sum_product, Finset.range_one, Finset.sum_singleton] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact normalizedKernel_derivative_integral_bound f L c C hC hL j

def kernelFourierConstant (f : SchwartzMap Space ℂ) (C : ℝ) (n : ℕ) : ℝ :=
  1 + 2 ^ n * (kernelDerivativeConstant f C 0 * weightNormalization +
    2 ^ n * ∑ j ∈ Finset.range (n + 1), kernelDerivativeConstant f C j * weightNormalization)

theorem kernelFourierConstant_pos (f : SchwartzMap Space ℂ) (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    0 < kernelFourierConstant f C n := by
  have h0 := kernelDerivativeConstant_nonneg f C hC 0
  have hmass := weightNormalization_pos
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), kernelDerivativeConstant f C j * weightNormalization :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (kernelDerivativeConstant_nonneg f C hC j)
      weightNormalization_pos.le)
  unfold kernelFourierConstant
  positivity

/-- Uniform Fourier decay for a translated linearly distorted Schwartz factor
times the actual fixed envelope weight. No seminorm depending on c or L occurs. -/
theorem normalizedKernel_fourier_decay_nat (f : SchwartzMap Space ℂ)
    (L : Space →L[ℝ] Space) (c : Space) (C : ℝ) (hC : 0 ≤ C) (hL : ‖L‖ ≤ C)
    (n : ℕ) (η : Space) :
    (1 + ‖η‖) ^ n * ‖𝓕 (normalizedKernel f L c) η‖ ≤ kernelFourierConstant f C n := by
  have h0 := kernelDerivativeConstant_nonneg f C hC 0
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), kernelDerivativeConstant f C j * weightNormalization :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (kernelDerivativeConstant_nonneg f C hC j)
      weightNormalization_pos.le)
  have hp := normalizedKernel_fourier_poly_bound f L c C hC hL n η
  have hbasic : ‖𝓕 (normalizedKernel f L c) η‖ ≤ kernelDerivativeConstant f C 0 * weightNormalization := by
    have hh := normalizedKernel_fourier_poly_bound f L c C hC hL 0 η
    simpa using hh
  by_cases hη : ‖η‖ ≤ 1
  · have hpow : (1 + ‖η‖) ^ n ≤ (2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have hh := mul_le_mul hpow hbasic (norm_nonneg _)
      (by positivity : 0 ≤ (2 : ℝ) ^ n)
    have hrest : 0 ≤ (2 : ℝ) ^ n * (2 ^ n *
        ∑ j ∈ Finset.range (n + 1), kernelDerivativeConstant f C j * weightNormalization) := by
      positivity
    unfold kernelFourierConstant
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]
  · have hpow : (1 + ‖η‖) ^ n ≤ (2 * ‖η‖) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at hpow
    have hh := mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 (normalizedKernel f L c) η))
    have hh' := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2 : ℝ) ^ n)
    unfold kernelFourierConstant
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n,
      mul_nonneg h0 weightNormalization_pos.le]

/-- The arbitrary positive real exponent version of the normalized kernel
estimate. The constant precedes the center and the linear map. -/
theorem normalizedKernel_fourier_decay (f : SchwartzMap Space ℂ) (C A : ℝ) (hC : 0 ≤ C)
    (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ (L : Space →L[ℝ] Space), ‖L‖ ≤ C → ∀ c η : Space,
        ‖𝓕 (normalizedKernel f L c) η‖ ≤ D * (1 + ‖η‖) ^ (-A) := by
  let n : ℕ := ⌈A⌉₊
  refine ⟨kernelFourierConstant f C n, kernelFourierConstant_pos f C hC n, ?_⟩
  intro L hL c η
  have hn : A ≤ (n : ℝ) := Nat.le_ceil A
  have hbase : 0 < 1 + ‖η‖ := by positivity
  have hpow : (1 + ‖η‖) ^ A ≤ (1 + ‖η‖) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg η]) hn
  have hh := mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 (normalizedKernel f L c) η))
  have hbound := hh.trans (normalizedKernel_fourier_decay_nat f L c C hC hL n η)
  rw [Real.rpow_neg hbase.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hbase A)]
  simpa only [mul_comm] using hbound

def squareCutoff (χ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  FourierLocalization.schwartzMul χ (FourierLocalization.schwartzConj χ)

theorem squareCutoff_apply (χ : SchwartzMap Space ℂ) (x : Space) :
    squareCutoff χ x = (‖χ x‖ ^ 2 : ℝ) := by
  simp [squareCutoff, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The actual squared cutoff and the actual polynomial weight, with uniform
center and distortion constants; no derivative hypothesis remains. -/
theorem actual_normalized_kernel_decay (χ : SchwartzMap Space ℂ) (C A : ℝ)
    (hC : 0 ≤ C) (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ (L : Space →L[ℝ] Space), ‖L‖ ≤ C → ∀ c η : Space,
        ‖𝓕 (fun u => ((‖χ (c + L u)‖ ^ 2 : ℝ) : ℂ) * (baseWeight u : ℂ)) η‖ ≤
          D * (1 + ‖η‖) ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := normalizedKernel_fourier_decay (squareCutoff χ) C A hC hA
  refine ⟨D, hD, ?_⟩
  intro L hL c η
  have hh := hb L hL c η
  have heq : normalizedKernel (squareCutoff χ) L c =
      fun u => ((‖χ (c + L u)‖ ^ 2 : ℝ) : ℂ) * (baseWeight u : ℂ) := by
    ext u
    unfold normalizedKernel schwartzAffine
    rw [squareCutoff_apply]
  rw [heq] at hh
  exact hh

theorem actual_scaled_kernel_decay (χ : SchwartzMap Space ℂ) (C A : ℝ)
    (hC : 0 ≤ C) (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ P : ℝ, 0 < P → ∀ (B : Space →L[ℝ] Space), ‖B‖ ≤ C * P →
      ∀ z₀ η : Space,
        ‖𝓕 (fun u => ((‖χ (P⁻¹ • (z₀ + B u))‖ ^ 2 : ℝ) : ℂ) * (baseWeight u : ℂ)) η‖ ≤
          D * (1 + ‖η‖) ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := actual_normalized_kernel_decay χ C A hC hA
  refine ⟨D, hD, ?_⟩
  intro P hP B hB z₀ η
  have hL : ‖P⁻¹ • B‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hP, inv_mul_eq_div,
      div_le_iff₀ hP]
    exact hB
  simpa only [ContinuousLinearMap.smul_apply, ← smul_add] using hb (P⁻¹ • B) hL (P⁻¹ • z₀) η

end
end CircleDivisor.EnergyV3.KernelBounds
