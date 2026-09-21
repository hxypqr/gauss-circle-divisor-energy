import CircleDivisor.FourierLocalization

/-! Actual physical-transpose transport to the circular coordinates used by
Guth--Maldague. The Jacobian is a single fixed positive constant. -/
namespace CircleDivisor.EnergyV3.LinearTransport
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
abbrev Space := FourierLocalization.Space

def circularPhysicalLinear : Space →ₗ[ℝ] Space where
  toFun y := WithLp.toLp 2 ![(3/5)*((y 2-y 1)/2), (3/5)*y 0, (3/5)*((y 2+y 1)/2)]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

def circularPhysicalInverse (z : Space) : Space :=
  WithLp.toLp 2 ![(5/3)*z 1, (5/3)*(z 2-z 0), (5/3)*(z 2+z 0)]

theorem circularPhysical_left_inverse (x : Space) :
    circularPhysicalInverse (circularPhysicalLinear x) = x := by
  ext i
  fin_cases i <;> simp [circularPhysicalInverse, circularPhysicalLinear] <;> ring

theorem circularPhysical_right_inverse (x : Space) :
    circularPhysicalLinear (circularPhysicalInverse x) = x := by
  ext i
  fin_cases i <;> simp [circularPhysicalInverse, circularPhysicalLinear] <;> ring

def circularPhysical : Space ≃L[ℝ] Space :=
  ({ circularPhysicalLinear with
      invFun := circularPhysicalInverse
      left_inv := circularPhysical_left_inverse
      right_inv := circularPhysical_right_inverse } : Space ≃ₗ[ℝ] Space).toContinuousLinearEquiv

def circularFrequency (v : Space) : Space :=
  WithLp.toLp 2 ![(3/5)*v 1, (3/5)*((v 2-v 0)/2), (3/5)*((v 2+v 0)/2)]

theorem transpose_pairing (y ξ : Space) :
    ⟪circularPhysical y, ξ⟫ = ⟪y, circularFrequency ξ⟫ := by
  simp [circularPhysical, circularPhysicalLinear, circularFrequency, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

def jacobian (e : Space ≃L[ℝ] Space) : ℝ := |LinearMap.det (e.symm : Space →ₗ[ℝ] Space)|

theorem jacobian_pos (e : Space ≃L[ℝ] Space) : 0 < jacobian e :=
  abs_pos.mpr (LinearEquiv.isUnit_det' e.symm.toLinearEquiv).ne_zero

theorem map_volume (e : Space ≃L[ℝ] Space) :
    Measure.map e volume = ENNReal.ofReal (jacobian e) • volume := by
  change Measure.map (e : Space →ₗ[ℝ] Space) volume = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (f := (e : Space →ₗ[ℝ] Space)) volume
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero]
  congr 2
  exact (congrArg abs (LinearEquiv.det_coe_symm e.toLinearEquiv)).symm

theorem integral_comp (e : Space ≃L[ℝ] Space) (f : Space → ℝ) :
    (∫ y, f (e y)) = jacobian e * ∫ z, f z := by
  have hh := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) f
  change (∫ z, f z ∂Measure.map e volume) = ∫ y, f (e y) at hh
  rw [← hh, map_volume, integral_smul_measure, ENNReal.toReal_ofReal (jacobian_pos e).le, smul_eq_mul]

theorem integrable_comp_iff (e : Space ≃L[ℝ] Space) (f : Space → ℝ) :
    Integrable (fun y => f (e y)) ↔ Integrable f := by
  have hh := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff (μ := volume) (g := f)
  change Integrable f (Measure.map e volume) ↔ Integrable (fun y => f (e y)) at hh
  rw [map_volume, integrable_smul_measure (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (jacobian_pos e))) ENNReal.ofReal_ne_top] at hh
  exact hh.symm

theorem memLp_comp {f : Space → ℂ} {p : ℝ≥0∞} (e : Space ≃L[ℝ] Space) (hf : MemLp f p volume) :
    MemLp (fun y => f (e y)) p volume := by
  have hm : MemLp f p (Measure.map e volume) := by rw [map_volume]; exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map e.continuous.measurable.aemeasurable

theorem pairSum_comp {ι : Type*} (P : Finset (ι × ι)) (f : ι → Space → ℂ)
    (e : Space ≃L[ℝ] Space) (y : Space) :
    FourierEnergy.pairSum P (fun i y => f i (e y)) y = FourierEnergy.pairSum P f (e y) := rfl

theorem pair_energy_comp {ι : Type*} (P : Finset (ι × ι)) (f : ι → Space → ℂ)
    (e : Space ≃L[ℝ] Space) :
    (∫ y, ‖FourierEnergy.pairSum P (fun i y => f i (e y)) y‖ ^ 2) =
      jacobian e * ∫ z, ‖FourierEnergy.pairSum P f z‖ ^ 2 :=
  integral_comp e (fun z => ‖FourierEnergy.pairSum P f z‖ ^ 2)

theorem moment_comp (e : Space ≃L[ℝ] Space) (f : Space → ℂ) (q : ℝ) :
    (∫ y, ‖f (e y)‖ ^ q) = jacobian e * ∫ z, ‖f z‖ ^ q := integral_comp e (fun z => ‖f z‖ ^ q)

end
end CircleDivisor.EnergyV3.LinearTransport
