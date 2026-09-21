import CircleDivisor.EnergyV3.SameRayEnergies

namespace CircleDivisor.EnergyV3.PairEnergies
open MeasureTheory Finset
open scoped ComplexConjugate
noncomputable section

theorem character_sub (d e : TorusProjection.Frequency) (u : TorusProjection.Torus) :
    TorusProjection.character (d-e) u =
      TorusProjection.character d u * conj (TorusProjection.character e u) := by
  change fourier (d.1-e.1) u.1 * fourier (d.2-e.2) u.2 = _
  simp only [TorusProjection.character, sub_eq_add_neg,
    fourier_add, fourier_neg, map_mul]
  ring

def atom (a : Point → ℂ) (p : Point) (u : TorusProjection.Torus) : ℂ :=
  a p * TorusProjection.character (projection p) u

/-- The weighted projection principle applies to the actual quadratic pair
sum, without requiring coefficients to be positive or real. -/
theorem pairSum_eq_polynomial (P : Finset Pair) (a : Point → ℂ) (u : TorusProjection.Torus) :
    FourierEnergy.pairSum P (atom a) u =
      TorusProjection.polynomial P difference (fun p => a p.1 * conj (a p.2)) u := by
  apply sum_congr rfl
  intro p hp
  dsimp [FourierEnergy.pairValue, atom, difference]
  rw [character_sub]
  simp only [map_mul]
  ring

theorem point_polynomial_mass (I : Finset Point) (a : Point → ℂ)
    (hI : ∀ p ∈ I, p.2 ≠ 0) :
    (∫ u, ‖∑ p ∈ I, atom a p u‖ ^ 2 ∂TorusProjection.haar) =
      ∑ p ∈ I, ‖a p‖ ^ 2 :=
  TorusProjection.parseval_injective I projection a (projection_injective hI)

theorem point_polynomial_mass_family {ι : Type*} (T : Finset ι) (I : ι → Finset Point)
    (hdisj : (T : Set ι).PairwiseDisjoint I) (a : Point → ℂ)
    (hI : ∀ i ∈ T, ∀ p ∈ I i, p.2 ≠ 0) :
    (∑ i ∈ T, ∫ u, ‖∑ p ∈ I i, atom a p u‖ ^ 2 ∂TorusProjection.haar) =
      ∑ p ∈ T.biUnion I, ‖a p‖ ^ 2 := by
  classical
  calc
    _ = ∑ i ∈ T, ∑ p ∈ I i, ‖a p‖ ^ 2 := sum_congr rfl (fun i hi => point_polynomial_mass (I i) a (hI i hi))
    _ = _ := (sum_biUnion hdisj).symm

theorem point_polynomial_mass_le_card (I : Finset Point) (a : Point → ℂ)
    (hI : ∀ p ∈ I, p.2 ≠ 0) (ha : ∀ p ∈ I, ‖a p‖ ≤ 1) :
    (∫ u, ‖∑ p ∈ I, atom a p u‖ ^ 2 ∂TorusProjection.haar) ≤ I.card := by
  rw [point_polynomial_mass I a hI]
  calc
    _ ≤ ∑ _p ∈ I, (1 : ℝ) := sum_le_sum (fun p hp => by nlinarith [ha p hp, norm_nonneg (a p)])
    _ = _ := by simp

def phasedCoefficient (a : Point → ℂ) (ω : Point → ℝ) (t : ℝ) (p : Point) : ℂ :=
  a p * Complex.exp ((2 * Real.pi * t * ω p : ℝ) * Complex.I)

theorem phasedCoefficient_norm (a : Point → ℂ) (ω : Point → ℝ) (t : ℝ) (p : Point) :
    ‖phasedCoefficient a ω t p‖ = ‖a p‖ := by
  simp only [phasedCoefficient, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Arbitrary third-coordinate phases preserve the exact mass identity at
every real `t`, not merely almost everywhere or after averaging. -/
theorem phased_mass (I : Finset Point) (a : Point → ℂ) (ω : Point → ℝ) (t : ℝ)
    (hI : ∀ p ∈ I, p.2 ≠ 0) :
    (∫ u, ‖∑ p ∈ I, atom (phasedCoefficient a ω t) p u‖ ^ 2 ∂TorusProjection.haar) =
      ∑ p ∈ I, ‖a p‖ ^ 2 := by
  simpa only [phasedCoefficient_norm] using point_polynomial_mass I (phasedCoefficient a ω t) hI

end
end CircleDivisor.EnergyV3.PairEnergies
