import CircleDivisor.EnergyV3.AngularAtoms

namespace CircleDivisor.EnergyV3.FourierTransport
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ENNReal
noncomputable section
abbrev Space := FourierLocalization.Space

theorem integral_comp_complex (e : Space ≃L[ℝ] Space) (f : Space → ℂ) :
    (∫ y, f (e y)) = LinearTransport.jacobian e • ∫ z, f z := by
  have hh := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) f
  change (∫ z, f z ∂Measure.map e volume) = ∫ y, f (e y) at hh
  rw [← hh, LinearTransport.map_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (LinearTransport.jacobian_pos e).le]

/-- Actual Fourier change of variables for any invertible physical linear map. -/
theorem fourier_comp (e : Space ≃L[ℝ] Space) (f : Space → ℂ) (η : Space) :
    𝓕 (fun y => f (e y)) η = LinearTransport.jacobian e •
      𝓕 f ((e.symm : Space →L[ℝ] Space).adjoint η) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hh := integral_comp_complex e (fun z =>
    Real.fourierChar (-⟪z,(e.symm : Space →L[ℝ] Space).adjoint η⟫) • f z)
  simpa only [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using hh

/-- Fourier support stays in the same ball when the physical map is a contraction.
The support conclusion follows from the actual Fourier transform formula. -/
theorem support_fourier_comp_contraction (e : Space ≃L[ℝ] Space)
    (he : ‖(e : Space →L[ℝ] Space)‖ ≤ 1) (f : Space → ℂ) (c : ℝ)
    (hf : Function.support (𝓕 f) ⊆ Metric.ball 0 c) :
    Function.support (𝓕 (fun y => f (e y))) ⊆ Metric.ball 0 c := by
  intro η hη
  have hn : 𝓕 f ((e.symm : Space →L[ℝ] Space).adjoint η) ≠ 0 := by
    intro hz
    exact hη (by rw [fourier_comp, hz, smul_zero])
  have hh := hf hn
  rw [Metric.mem_ball, dist_zero_right] at hh ⊢
  have heq : (e : Space →L[ℝ] Space).adjoint ((e.symm : Space →L[ℝ] Space).adjoint η) = η := by
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    simp
  have hb := (e : Space →L[ℝ] Space).adjoint.le_opNorm ((e.symm : Space →L[ℝ] Space).adjoint η)
  rw [heq, ContinuousLinearMap.adjoint.norm_map] at hb
  exact (hb.trans (by nlinarith [norm_nonneg ((e.symm : Space →L[ℝ] Space).adjoint η)])).trans_lt hh

def rotationLinear (ρ : ℝ) : Space →ₗ[ℝ] Space where
  toFun := AngularAtoms.rotate ρ
  map_add' x y := by ext i; fin_cases i <;> simp [AngularAtoms.rotate] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [AngularAtoms.rotate] <;> ring

def rotation (ρ : ℝ) : Space ≃L[ℝ] Space :=
  ({ rotationLinear ρ with
    invFun := AngularAtoms.rotate (-ρ)
    left_inv := AngularAtoms.rotate_neg_rotate ρ
    right_inv := by
      intro v
      change AngularAtoms.rotate ρ (AngularAtoms.rotate (-ρ) v) = v
      simpa using AngularAtoms.rotate_neg_rotate (-ρ) v } : Space ≃ₗ[ℝ] Space).toContinuousLinearEquiv

def rotatedPhysical (ρ : ℝ) : Space ≃L[ℝ] Space :=
  (rotation (-ρ)).trans LinearTransport.circularPhysical

theorem circularPhysical_norm_le (v : Space) : ‖LinearTransport.circularPhysical v‖ ≤ ‖v‖ := by
  have ha := EuclideanSpace.real_norm_sq_eq (LinearTransport.circularPhysical v)
  have hb := EuclideanSpace.real_norm_sq_eq v
  simp only [Fin.sum_univ_succ] at ha
  simp [Fin.sum_univ_succ] at hb
  change ‖LinearTransport.circularPhysical v‖^2 =
    ((3/5)*((v 2-v 1)/2))^2+(((3/5)*v 0)^2+(((3/5)*((v 2+v 1)/2))^2+0)) at ha
  nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2),
    norm_nonneg v,norm_nonneg (LinearTransport.circularPhysical v)]

theorem rotatedPhysical_contraction (ρ : ℝ) :
    ‖(rotatedPhysical ρ : Space →L[ℝ] Space)‖ ≤ 1 := by
  apply (rotatedPhysical ρ : Space →L[ℝ] Space).opNorm_le_bound (by norm_num : (0:ℝ) ≤ 1)
  intro v
  change ‖LinearTransport.circularPhysical (AngularAtoms.rotate (-ρ) v)‖ ≤ 1*‖v‖
  calc
    _ ≤ ‖AngularAtoms.rotate (-ρ) v‖ := circularPhysical_norm_le _
    _ = _ := by rw [AngularAtoms.rotate_norm, one_mul]

theorem rotatedPhysical_pairing (ρ : ℝ) (v ξ : Space) :
    ⟪rotatedPhysical ρ v, ξ⟫ =
      ⟪v, AngularAtoms.rotate ρ (LinearTransport.circularFrequency ξ)⟫ := by
  change ⟪LinearTransport.circularPhysical (AngularAtoms.rotate (-ρ) v),ξ⟫ = _
  rw [LinearTransport.transpose_pairing]
  simp [AngularAtoms.rotate, PiLp.inner_apply, Fin.sum_univ_succ, Real.cos_neg, Real.sin_neg]
  ring

theorem support_rotated_cutoff (ρ : ℝ) (χ : Space → ℂ) (c : ℝ)
    (hχ : Function.support (𝓕 χ) ⊆ Metric.ball 0 c) :
    Function.support (𝓕 (fun y => χ (rotatedPhysical ρ y))) ⊆ Metric.ball 0 c :=
  support_fourier_comp_contraction _ (rotatedPhysical_contraction ρ) χ c hχ

set_option maxHeartbeats 1000000 in
def rotationIsometry (ρ : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  { (rotation ρ).toLinearEquiv with norm_map' := AngularAtoms.rotate_norm ρ }

set_option maxHeartbeats 1000000 in
theorem integral_rotatedPhysical (ρ : ℝ) (f : Space → ℝ) :
    (∫ y, f (rotatedPhysical ρ y)) = LinearTransport.jacobian LinearTransport.circularPhysical * ∫ z, f z := by
  have heq : (fun y => f (rotatedPhysical ρ y)) =
      fun y => (fun z => f (LinearTransport.circularPhysical z)) (rotationIsometry (-ρ) y) := rfl
  rw [heq]
  rw [(rotationIsometry (-ρ)).measurePreserving.integral_comp
    (rotationIsometry (-ρ)).toHomeomorph.measurableEmbedding (fun z => f (LinearTransport.circularPhysical z))]
  exact LinearTransport.integral_comp LinearTransport.circularPhysical f

end
end CircleDivisor.EnergyV3.FourierTransport
