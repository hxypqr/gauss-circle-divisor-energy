import CircleDivisor.EnergyV3.FourierTransport
import CircleDivisor.EnergyV3.WeightMass

/-! A rotation has no effect on the fixed physical change-of-variables factor.
We compare its action on the indicator of a set of volume one. -/
namespace CircleDivisor.EnergyV3.RotationJacobian
noncomputable section
open MeasureTheory

theorem rotatedPhysical_jacobian (ρ : ℝ) :
    LinearTransport.jacobian (FourierTransport.rotatedPhysical ρ) =
      LinearTransport.jacobian LinearTransport.circularPhysical := by
  have hm : MeasurableSet WeightMass.unitCube := by
    unfold WeightMass.unitCube
    simp_rw [Set.setOf_forall]
    have hc (k : Fin 3) : Continuous (fun x : FourierLocalization.Space => |x k|) := by fun_prop
    exact MeasurableSet.iInter (fun k => measurableSet_le (hc k).measurable measurable_const)
  let f : FourierLocalization.Space→ℝ := WeightMass.unitCube.indicator (fun _ => 1)
  have hf : (∫ x, f x)=1 := by
    change (∫ x, WeightMass.unitCube.indicator (1 : FourierLocalization.Space→ℝ) x)=1
    rw [integral_indicator_one hm]
    simp only [Measure.real,WeightMass.unitCube_volume,ENNReal.toReal_one]
  have h1 := LinearTransport.integral_comp (FourierTransport.rotatedPhysical ρ) f
  have h2 := FourierTransport.integral_rotatedPhysical ρ f
  rw [hf,mul_one] at h1 h2
  exact h1.symm.trans h2

end
end CircleDivisor.EnergyV3.RotationJacobian
