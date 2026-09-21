import CircleDivisor.EnergyV3.CanonicalLocalization

namespace CircleDivisor.EnergyV3.ClassDecomposition
open MeasureTheory Finset FourierTransform
open scoped ENNReal
noncomputable section
abbrev Space := FourierLocalization.Space
abbrev Point := CanonicalLocalization.Point

def originalAtom (K L : ℝ) (χ : SchwartzMap Space ℂ) (p : Point) (z : Space) : ℂ :=
  FourierLocalization.dilate (K*L) χ z *
    FourierLocalization.character (FourierLocalization.coneFrequency K L p.1 p.2) z

def originalSum (K L : ℝ) (χ : SchwartzMap Space ℂ) (I : Finset Point)
    (coeff : Point → ℂ) (z : Space) : ℂ := ∑ p ∈ I, coeff p*originalAtom K L χ p z

theorem localizedSchwartz_comp (K L ρ : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap Space ℂ)
    (I : Finset Point) (coeff : Point → ℂ) (y : Space) :
    CanonicalLocalization.localizedSchwartz K L ρ hP χ I coeff y =
      originalSum K L χ I coeff (FourierTransport.rotatedPhysical ρ y) := by
  rw [CanonicalLocalization.localizedSchwartz_coe]
  rfl

theorem originalSum_full (K L : ℝ) (χ : SchwartzMap Space ℂ) (a : ℤ → ℤ → ℂ) :
    originalSum K L χ ((dyadicIntegers K).product (dyadicIntegers L)) (fun p => a p.1 p.2) =
      LocalizationNormalization.localized K L χ a := by
  funext z
  change (∑ p ∈ (dyadicIntegers K) ×ˢ (dyadicIntegers L), a p.1 p.2*originalAtom K L χ p z) = _
  simp only [originalSum, originalAtom, LocalizationNormalization.localized,
    LocalizationNormalization.unlocalized, Finset.mul_sum]
  rw [Finset.sum_product (dyadicIntegers K) (dyadicIntegers L)
    (fun p : Point => a p.1 p.2*(FourierLocalization.dilate (K*L) χ z*
      FourierLocalization.character (FourierLocalization.coneFrequency K L p.1 p.2) z))]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Exact two-class decomposition in the original normalized coordinates. -/
theorem original_two_classes (K L : ℝ) (χ : SchwartzMap Space ℂ) (a : ℤ → ℤ → ℂ) (b : ℤ → Bool) :
    LocalizationNormalization.localized K L χ a = fun z =>
      originalSum K L χ (CanonicalLocalization.classPoints K L b false) (fun p => a p.1 p.2) z+
      originalSum K L χ (CanonicalLocalization.classPoints K L b true) (fun p => a p.1 p.2) z := by
  rw [← originalSum_full K L χ a]
  funext z
  exact (CanonicalLocalization.classPoints_partition K L b (fun p => a p.1 p.2*originalAtom K L χ p z)).symm

/-- The two rotated classes have exactly the same fixed Jacobian factor. -/
theorem class_moment_transport (K L ρ q : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap Space ℂ)
    (I : Finset Point) (coeff : Point → ℂ) :
    (∫ y, ‖CanonicalLocalization.localizedSchwartz K L ρ hP χ I coeff y‖^q) =
      LinearTransport.jacobian LinearTransport.circularPhysical *
        ∫ z, ‖originalSum K L χ I coeff z‖^q := by
  simp_rw [localizedSchwartz_comp]
  exact FourierTransport.integral_rotatedPhysical ρ (fun z => ‖originalSum K L χ I coeff z‖^q)

def originalSchwartz (K L : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap Space ℂ)
    (I : Finset Point) (coeff : Point → ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (FourierTransport.rotatedPhysical 0).symm
    (CanonicalLocalization.localizedSchwartz K L 0 hP χ I coeff)

theorem originalSchwartz_coe (K L : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap Space ℂ)
    (I : Finset Point) (coeff : Point → ℂ) :
    (originalSchwartz K L hP χ I coeff : Space → ℂ) = originalSum K L χ I coeff := by
  funext z
  change CanonicalLocalization.localizedSchwartz K L 0 hP χ I coeff ((FourierTransport.rotatedPhysical 0).symm z) = _
  rw [localizedSchwartz_comp, ContinuousLinearEquiv.apply_symm_apply]

theorem originalSum_integrable_norm_rpow (K L q : ℝ) (hP : K*L ≠ 0) (hq : 0 < q)
    (χ : SchwartzMap Space ℂ) (I : Finset Point) (coeff : Point → ℂ) :
    Integrable (fun z => ‖originalSum K L χ I coeff z‖^q) := by
  let f := originalSchwartz K L hP χ I coeff
  have hf := (f.memLp (ENNReal.ofReal q)).integrable_norm_rpow
    (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hq.le] at hf
  simpa only [f, originalSchwartz_coe] using hf

theorem jacobian_trans (e f : Space ≃L[ℝ] Space) :
    LinearTransport.jacobian (e.trans f) = LinearTransport.jacobian e*LinearTransport.jacobian f := by
  change |LinearMap.det ((e.symm : Space →ₗ[ℝ] Space).comp (f.symm : Space →ₗ[ℝ] Space))| = _
  rw [LinearMap.det_comp,abs_mul]
  rfl

theorem jacobian_rotation (ρ : ℝ) : LinearTransport.jacobian (FourierTransport.rotation ρ) = 1 := by
  have h := (FourierTransport.rotationIsometry ρ).symm.toLinearIsometry.normDet_eq_one
  rw [LinearMap.normDet_eq_abs_det] at h
  exact h

theorem jacobian_rotatedPhysical (ρ : ℝ) :
    LinearTransport.jacobian (FourierTransport.rotatedPhysical ρ) =
      LinearTransport.jacobian LinearTransport.circularPhysical := by
  rw [FourierTransport.rotatedPhysical, jacobian_trans, jacobian_rotation,one_mul]

end
end CircleDivisor.EnergyV3.ClassDecomposition
