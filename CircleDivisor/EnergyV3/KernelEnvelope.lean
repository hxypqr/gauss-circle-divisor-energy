import CircleDivisor.EnergyV3.KernelActual
import CircleDivisor.EnergyV3.WeightGeometry

namespace CircleDivisor.EnergyV3.KernelEnvelope
noncomputable section
open GuthMaldague KernelActual
open scoped FourierTransform

def synthesisEquiv (n j : ℕ) (i : CapIndex j) : Space ≃L[ℝ] Space :=
  (WeightMass.coordinateEquiv (radius n) (scale j) (leftEndpoint j i)
    (radius_pos n).ne' (scale_pos j).ne').symm

def envelopeKernel (χ : SchwartzMap Space ℂ) (P : ℝ)
    (n j : ℕ) (i : CapIndex j) (m : Lattice) : Space → ℂ :=
  fun z => ((‖χ (P⁻¹ • z)‖ ^ 2 : ℝ) : ℂ) * (envelopeWeight n j i m z : ℂ)

theorem envelopeKernel_eq (χ : SchwartzMap Space ℂ) (P : ℝ)
    (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    envelopeKernel χ P n j i m = (weightNormalization⁻¹ : ℂ) •
      physicalKernel χ P (synthesisEquiv n j i) (envelopeCenter n j i m) := by
  ext z
  simp only [envelopeKernel, Pi.smul_apply, smul_eq_mul, physicalKernel]
  change ((‖χ (P⁻¹ • z)‖ ^ 2 : ℝ) : ℂ) *
      ((baseWeight (WithLp.toLp 2 (envelopeCoordinates (radius n) (scale j) (leftEndpoint j i)
        (z - envelopeCenter n j i m))) / weightNormalization : ℝ) : ℂ) = _
  simp only [synthesisEquiv, ContinuousLinearEquiv.symm_symm]
  change _ = (weightNormalization⁻¹ : ℂ) *
    (((‖χ (P⁻¹ • z)‖ ^ 2 : ℝ) : ℂ) *
      (baseWeight (WithLp.toLp 2 (envelopeCoordinates (radius n) (scale j) (leftEndpoint j i)
        (z - envelopeCenter n j i m))) : ℂ))
  push_cast
  ring

theorem jacobian_synthesis (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    KernelActual.jacobian (synthesisEquiv n j i) = envelopeVolume n j i m := by
  rw [WeightMass.envelopeVolume_eq]
  rfl

/-- The actual canonical envelope version of Appendix A.5, with exactly the
weight and volume used by the Guth--Maldague interface. -/
theorem envelope_kernel_decay (χ : SchwartzMap Space ℂ) (C A : ℝ)
    (hC : 0 ≤ C) (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ P : ℝ, 0 < P → ∀ n j : ℕ, ∀ i : CapIndex j,
        ‖(synthesisEquiv n j i : Space →L[ℝ] Space)‖ ≤ C * P →
        ∀ (m : Lattice) (ν : Space),
          ‖𝓕 (envelopeKernel χ P n j i m) ν‖ ≤ D * envelopeVolume n j i m *
            (1 + ‖(synthesisEquiv n j i : Space →L[ℝ] Space).adjoint ν‖) ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := physical_kernel_decay χ C A hC hA
  refine ⟨D / weightNormalization, div_pos hD weightNormalization_pos, ?_⟩
  intro P hP n j i hB m ν
  rw [envelopeKernel_eq]
  change ‖𝓕 (fun z => (weightNormalization⁻¹ : ℂ) *
    physicalKernel χ P (synthesisEquiv n j i) (envelopeCenter n j i m) z) ν‖ ≤ _
  rw [fourier_const_mul, norm_mul]
  have hnorm : ‖(weightNormalization⁻¹ : ℂ)‖ = weightNormalization⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos weightNormalization_pos]
  rw [hnorm]
  have hh := mul_le_mul_of_nonneg_left
    (hb P hP (synthesisEquiv n j i) hB (envelopeCenter n j i m) ν)
    (inv_nonneg.mpr weightNormalization_pos.le)
  rw [jacobian_synthesis n j i m] at hh
  convert hh using 1 <;> first | ring | rfl

theorem canonical_envelope_kernel_decay (χ : SchwartzMap Space ℂ) (A : ℝ)
    (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ P : ℝ, 0 < P → ∀ n j : ℕ, ∀ i : CapIndex j, radius n < 4*P →
        ∀ (m : Lattice) (ν : Space),
          ‖𝓕 (envelopeKernel χ P n j i m) ν‖ ≤ D * envelopeVolume n j i m *
            (1 + ‖(synthesisEquiv n j i : Space →L[ℝ] Space).adjoint ν‖) ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := envelope_kernel_decay χ 24 A (by norm_num) hA
  exact ⟨D, hD, fun P hP n j i hR m ν => hb P hP n j i
    (WeightGeometry.canonical_synthesis_norm_le P n j i hR) m ν⟩

def transportedEnvelopeKernel (χ : SchwartzMap Space ℂ) (P : ℝ)
    (E : Space →L[ℝ] Space) (n j : ℕ) (i : CapIndex j) (m : Lattice) : Space → ℂ :=
  fun z => ((‖χ (P⁻¹ • E z)‖ ^ 2 : ℝ) : ℂ) * (envelopeWeight n j i m z : ℂ)

theorem transportedEnvelopeKernel_eq (χ : SchwartzMap Space ℂ) (P : ℝ)
    (E : Space →L[ℝ] Space) (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    transportedEnvelopeKernel χ P E n j i m = fun z => (weightNormalization⁻¹ : ℂ) *
      transportedPhysicalKernel χ P E (synthesisEquiv n j i) (envelopeCenter n j i m) z := by
  ext z
  simp only [transportedEnvelopeKernel, transportedPhysicalKernel]
  change ((‖χ (P⁻¹ • E z)‖ ^ 2 : ℝ) : ℂ) *
      ((baseWeight (WithLp.toLp 2 (envelopeCoordinates (radius n) (scale j) (leftEndpoint j i)
        (z - envelopeCenter n j i m))) / weightNormalization : ℝ) : ℂ) = _
  simp only [synthesisEquiv, ContinuousLinearEquiv.symm_symm]
  change _ = (weightNormalization⁻¹ : ℂ) *
    (((‖χ (P⁻¹ • E z)‖ ^ 2 : ℝ) : ℂ) *
      (baseWeight (WithLp.toLp 2 (envelopeCoordinates (radius n) (scale j) (leftEndpoint j i)
        (z - envelopeCenter n j i m))) : ℂ))
  push_cast
  ring

theorem transported_envelope_kernel_decay (χ : SchwartzMap Space ℂ) (C₀ A : ℝ)
    (hC₀ : 0 ≤ C₀) (hA : 0 < A) : ∃ D : ℝ, 0 < D ∧
      ∀ P : ℝ, 0 < P → ∀ E : Space →L[ℝ] Space, ‖E‖ ≤ C₀ →
      ∀ n j : ℕ, ∀ i : CapIndex j, radius n < 4*P → ∀ (m : Lattice) (ν : Space),
        ‖𝓕 (transportedEnvelopeKernel χ P E n j i m) ν‖ ≤ D * envelopeVolume n j i m *
          (1 + ‖(synthesisEquiv n j i : Space →L[ℝ] Space).adjoint ν‖) ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := transported_physical_kernel_decay χ 24 C₀ A (by norm_num) hC₀ hA
  refine ⟨D / weightNormalization, div_pos hD weightNormalization_pos, ?_⟩
  intro P hP E hE n j i hR m ν
  rw [transportedEnvelopeKernel_eq, fourier_const_mul, norm_mul]
  have hnorm : ‖(weightNormalization⁻¹ : ℂ)‖ = weightNormalization⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos weightNormalization_pos]
  rw [hnorm]
  have hh := mul_le_mul_of_nonneg_left
    (hb P hP E hE (synthesisEquiv n j i)
      (WeightGeometry.canonical_synthesis_norm_le P n j i hR) (envelopeCenter n j i m) ν)
    (inv_nonneg.mpr weightNormalization_pos.le)
  rw [jacobian_synthesis n j i m] at hh
  convert hh using 1 <;> first | ring | rfl

end
end CircleDivisor.EnergyV3.KernelEnvelope


