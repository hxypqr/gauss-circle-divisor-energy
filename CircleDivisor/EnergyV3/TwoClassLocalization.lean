import CircleDivisor.EnergyV3.ClassDecomposition
import CircleDivisor.EnergyV3.AmplitudeConstants

namespace CircleDivisor.EnergyV3.TwoClassLocalization
open MeasureTheory
noncomputable section
abbrev Space := FourierLocalization.Space

theorem localized_moment_le_two_classes (K L q : ℝ) (hP : K*L ≠ 0)
    (hq : 0 < q) (hqu : q ≤ 5) (χ : SchwartzMap Space ℂ) (a : ℤ → ℤ → ℂ)
    (b : ℤ → Bool) (ρ : Bool → ℝ) :
    (∫ z, ‖LocalizationNormalization.localized K L χ a z‖^q) ≤
      (32/LinearTransport.jacobian LinearTransport.circularPhysical)*
        ((∫ y, ‖CanonicalLocalization.localizedSchwartz K L (ρ false) hP χ
          (CanonicalLocalization.classPoints K L b false) (fun p => a p.1 p.2) y‖^q)+
         (∫ y, ‖CanonicalLocalization.localizedSchwartz K L (ρ true) hP χ
          (CanonicalLocalization.classPoints K L b true) (fun p => a p.1 p.2) y‖^q)) := by
  let f (d : Bool) := ClassDecomposition.originalSum K L χ
    (CanonicalLocalization.classPoints K L b d) (fun p => a p.1 p.2)
  have hc (d : Bool) : Continuous (f d) := by
    rw [show f d = (ClassDecomposition.originalSchwartz K L hP χ
        (CanonicalLocalization.classPoints K L b d) (fun p => a p.1 p.2) : Space → ℂ)
      from (ClassDecomposition.originalSchwartz_coe K L hP χ _ _).symm]
    exact (ClassDecomposition.originalSchwartz K L hP χ _ _).continuous
  have hi (d : Bool) : Integrable (fun z => ‖f d z‖^q) :=
    ClassDecomposition.originalSum_integrable_norm_rpow K L q hP hq χ _ _
  have hadd := AmplitudeConstants.moment_add hq.le hqu (f false) (f true) (hc false) (hc true) (hi false) (hi true)
  have hj := LinearTransport.jacobian_pos LinearTransport.circularPhysical
  calc
    _ = ∫ z, ‖f false z+f true z‖^q := by rw [ClassDecomposition.original_two_classes K L χ a b]
    _ ≤ 32*((∫ z, ‖f false z‖^q)+(∫ z, ‖f true z‖^q)) := hadd.2
    _ = _ := by
      rw [ClassDecomposition.class_moment_transport,ClassDecomposition.class_moment_transport]
      dsimp [f]
      field_simp
      <;> ring

theorem localized_moment_le_uniform_classes (K L q B : ℝ) (hP : K*L ≠ 0)
    (hq : 0 < q) (hqu : q ≤ 5) (χ : SchwartzMap Space ℂ) (a : ℤ → ℤ → ℂ)
    (b : ℤ → Bool) (ρ : Bool → ℝ)
    (hbound : ∀ d : Bool, (∫ y, ‖CanonicalLocalization.localizedSchwartz K L (ρ d) hP χ
      (CanonicalLocalization.classPoints K L b d) (fun p => a p.1 p.2) y‖^q) ≤ B) :
    (∫ z, ‖LocalizationNormalization.localized K L χ a z‖^q) ≤
      (64/LinearTransport.jacobian LinearTransport.circularPhysical)*B := by
  have hh := localized_moment_le_two_classes K L q hP hq hqu χ a b ρ
  have hj := LinearTransport.jacobian_pos LinearTransport.circularPhysical
  have hm := mul_le_mul_of_nonneg_left (add_le_add (hbound false) (hbound true))
    (show 0 ≤ 32/LinearTransport.jacobian LinearTransport.circularPhysical by positivity)
  exact hh.trans (hm.trans_eq (by ring))

end
end CircleDivisor.EnergyV3.TwoClassLocalization
