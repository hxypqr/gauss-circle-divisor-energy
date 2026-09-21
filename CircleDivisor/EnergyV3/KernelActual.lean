import CircleDivisor.EnergyV3.KernelBounds

namespace CircleDivisor.EnergyV3.KernelActual
noncomputable section
open GuthMaldague KernelBounds MeasureTheory MeasureTheory.Measure
open scoped FourierTransform RealInnerProductSpace

def jacobian (B : Space ≃L[ℝ] Space) : ℝ := |LinearMap.det (B : Space →ₗ[ℝ] Space)|

theorem jacobian_pos (B : Space ≃L[ℝ] Space) : 0 < jacobian B :=
  abs_pos.mpr (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero

theorem fourier_const_mul (c : ℂ) (f : Space → ℂ) (ν : Space) :
    𝓕 (fun z => c * f z) ν = c * 𝓕 f ν := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Circle.smul_def]
  ring

theorem integral_linear_change (B : Space ≃L[ℝ] Space) (f : Space → ℂ) :
    (∫ z, f z) = (jacobian B : ℂ) * ∫ u, f (B u) := by
  have hmap : Measure.map B.symm volume = ENNReal.ofReal (jacobian B) • volume := by
    change Measure.map (B.symm : Space →ₗ[ℝ] Space) volume = _
    rw [map_linearMap_addHaar_eq_smul_addHaar
      (f := (B.symm : Space →ₗ[ℝ] Space)) volume
      (LinearEquiv.isUnit_det' B.symm.toLinearEquiv).ne_zero]
    simp [jacobian, LinearEquiv.det_coe_symm]
  have hh := B.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map
    (μ := volume) (fun u => f (B u))
  change (∫ u, f (B u) ∂Measure.map B.symm volume) = ∫ z, f (B (B.symm z)) at hh
  simp only [B.apply_symm_apply] at hh
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (jacobian_pos B).le] at hh
  simpa only [Complex.real_smul] using hh.symm

theorem integral_affine_change (B : Space ≃L[ℝ] Space) (z₀ : Space) (f : Space → ℂ) :
    (∫ z, f z) = (jacobian B : ℂ) * ∫ u, f (z₀ + B u) := by
  have ht : (∫ z : Space, f (z₀ + z)) = ∫ z : Space, f z := integral_add_left_eq_self f z₀
  rw [← ht]
  exact integral_linear_change B (fun z => f (z₀ + z))

/-- The full affine Fourier change of variables, including its phase and actual
Jacobian, for arbitrary complex functions. -/
theorem fourier_affine_change (B : Space ≃L[ℝ] Space) (z₀ ν : Space) (f : Space → ℂ) :
    𝓕 f ν = (jacobian B : ℂ) * (Real.fourierChar (-⟪z₀, ν⟫) : ℂ) *
      𝓕 (fun u => f (z₀ + B u)) ((B : Space →L[ℝ] Space).adjoint ν) := by
  rw [Real.fourier_eq]
  rw [integral_affine_change B z₀]
  rw [Real.fourier_eq, mul_assoc]
  apply congrArg (fun w : ℂ => (jacobian B : ℂ) * w)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [inner_add_left, neg_add_rev, Circle.smul_def]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [AddChar.map_add_eq_mul]
  push_cast
  ring

theorem norm_fourier_affine_change (B : Space ≃L[ℝ] Space) (z₀ ν : Space) (f : Space → ℂ) :
    ‖𝓕 f ν‖ = jacobian B *
      ‖𝓕 (fun u => f (z₀ + B u)) ((B : Space →L[ℝ] Space).adjoint ν)‖ := by
  rw [fourier_affine_change B z₀ ν f]
  simp [norm_mul, jacobian, abs_of_nonneg (abs_nonneg _)]

def physicalKernel (χ : SchwartzMap Space ℂ) (P : ℝ)
    (B : Space ≃L[ℝ] Space) (z₀ : Space) : Space → ℂ :=
  fun z => ((‖χ (P⁻¹ • z)‖ ^ 2 : ℝ) : ℂ) * (baseWeight (B.symm (z - z₀)) : ℂ)

/-- Appendix A.5 for actual envelope weights. The only size assumption is the
manuscript's upper bound on B/P, and the constant is chosen before P,B,z₀. -/
theorem physical_kernel_decay (χ : SchwartzMap Space ℂ) (C A : ℝ)
    (hC : 0 ≤ C) (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ P : ℝ, 0 < P → ∀ (B : Space ≃L[ℝ] Space), ‖(B : Space →L[ℝ] Space)‖ ≤ C * P →
      ∀ z₀ ν : Space,
        ‖𝓕 (physicalKernel χ P B z₀) ν‖ ≤
          D * jacobian B * (1 + ‖(B : Space →L[ℝ] Space).adjoint ν‖) ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := actual_scaled_kernel_decay χ C A hC hA
  refine ⟨D, hD, ?_⟩
  intro P hP B hB z₀ ν
  rw [norm_fourier_affine_change B z₀ ν]
  have heq : (fun u => physicalKernel χ P B z₀ (z₀ + B u)) =
      fun u => ((‖χ (P⁻¹ • (z₀ + B u))‖ ^ 2 : ℝ) : ℂ) * (baseWeight u : ℂ) := by
    ext u
    simp [physicalKernel, add_sub_cancel_left]
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left
    (hb P hP (B : Space →L[ℝ] Space) hB z₀ ((B : Space →L[ℝ] Space).adjoint ν))
    (jacobian_pos B).le
  calc
    _ ≤ jacobian B * (D * (1 + ‖(B : Space →L[ℝ] Space).adjoint ν‖) ^ (-A)) := hh
    _ = _ := by ring

def transportedPhysicalKernel (χ : SchwartzMap Space ℂ) (P : ℝ)
    (E : Space →L[ℝ] Space) (B : Space ≃L[ℝ] Space) (z₀ : Space) : Space → ℂ :=
  fun z => ((‖χ (P⁻¹ • E z)‖ ^ 2 : ℝ) : ℂ) * (baseWeight (B.symm (z - z₀)) : ℂ)

theorem transported_physical_kernel_decay (χ : SchwartzMap Space ℂ) (C C₀ A : ℝ)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ P : ℝ, 0 < P → ∀ (E : Space →L[ℝ] Space), ‖E‖ ≤ C₀ →
      ∀ (B : Space ≃L[ℝ] Space), ‖(B : Space →L[ℝ] Space)‖ ≤ C * P →
      ∀ z₀ ν : Space,
        ‖𝓕 (transportedPhysicalKernel χ P E B z₀) ν‖ ≤
          D * jacobian B * (1 + ‖(B : Space →L[ℝ] Space).adjoint ν‖) ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := actual_scaled_kernel_decay χ (C₀*C) A (mul_nonneg hC₀ hC) hA
  refine ⟨D, hD, ?_⟩
  intro P hP E hE B hB z₀ ν
  rw [norm_fourier_affine_change B z₀ ν]
  have heq : (fun u => transportedPhysicalKernel χ P E B z₀ (z₀ + B u)) =
      fun u => ((‖χ (P⁻¹ • (E z₀ + (E.comp (B : Space →L[ℝ] Space)) u))‖ ^ 2 : ℝ) : ℂ) *
        (baseWeight u : ℂ) := by ext u; simp [transportedPhysicalKernel, map_add]
  rw [heq]
  have hEB : ‖E.comp (B : Space →L[ℝ] Space)‖ ≤ C₀*C*P := by
    calc
      _ ≤ ‖E‖ * ‖(B : Space →L[ℝ] Space)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C₀ * (C*P) := mul_le_mul hE hB (norm_nonneg _) hC₀
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left
    (hb P hP _ hEB (E z₀) ((B : Space →L[ℝ] Space).adjoint ν)) (jacobian_pos B).le
  calc
    _ ≤ jacobian B * (D * (1 + ‖(B : Space →L[ℝ] Space).adjoint ν‖) ^ (-A)) := hh
    _ = _ := by ring

end
end CircleDivisor.EnergyV3.KernelActual
