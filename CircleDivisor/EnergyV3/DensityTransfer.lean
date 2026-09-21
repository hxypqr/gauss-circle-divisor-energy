import CircleDivisor.EnergyV3.LocalDensityActual
import CircleDivisor.EnergyV3.CoarseEnergy
import CircleDivisor.EnergyV3.CoarseWindows
import CircleDivisor.EnergyV3.AmplitudeScale

/-! Uniform local density for the actual same-ray mass and the actual signed
remainder in GM's partial square function. -/
namespace CircleDivisor.EnergyV3.DensityTransfer
noncomputable section
open GuthMaldague CoarseDecomposition
open scoped FourierTransform
abbrev Space := GuthMaldague.Space

theorem actual_mass_densities (χ : SchwartzMap Space ℂ) :
    ∃ A : ℝ, 1≤A ∧ ∀ K L c : ℝ, 1≤L → L≤K → 4*c≤1 →
      Function.support (𝓕 (χ : Space→ℂ)) ⊆ Metric.ball 0 c →
      ∀ n : ℕ, K*L≤radius n → radius n<4*(K*L) →
      ∀ ρ : ℝ, 0≤ρ → ρ≤1 → ∀ I : Finset Point, ∀ θ : ℤ→CapIndex n,
      (∀ p∈I, K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L) →
      (∀ p∈I, CoarseWindows.frequency K L ρ p∈cap n (θ p.1)) →
      ∀ a : Point→ℂ, (∀ p, ‖a p‖≤1) → ∀ f : Space→ℂ,
      (∀ b x, capFunction n b f x = ∑ p∈I.filter (fun p => θ p.1=b),
        CoarseEnergy.physicalAtoms K L χ a (FourierTransport.rotatedPhysical ρ) p x) →
      ∀ j ∈ Finset.Ioo 0 n, ∀ i : CapIndex j, ∀ m : Lattice,
        sameMass n j I θ (CoarseEnergy.physicalAtoms K L χ a (FourierTransport.rotatedPhysical ρ)) i m ≤
          A*CircleDivisor.ScaleBounds.D K L (scale j) ∧
        |localMass n j i m f -
          sameMass n j I θ (CoarseEnergy.physicalAtoms K L χ a (FourierTransport.rotatedPhysical ρ)) i m| ≤
          A*CircleDivisor.ScaleBounds.M K L (scale j) := by
  obtain ⟨C,hC,hden⟩ := LocalDensityActual.actual_local_density χ
  refine ⟨max C 1, le_max_right _ _,?_⟩
  intro K L c hL hLK hc hχ n hPR hRP ρ hρ hρ1 I θ hI hcap a ha f hsharp j hj i m
  have hK : 1≤K := hL.trans hLK
  have hK0 : 0<K := by linarith
  have hL0 : 0<L := by linarith
  have hP : 1≤K*L := one_le_mul_of_one_le_of_one_le hK hL
  have hsK : 1 ≤ scale j*K := by
    simpa only [one_mul] using
      (RefinedEnergy.widths hL hLK (AmplitudeScale.scale_range hP hRP hj).1 (le_refl (1:ℝ))).2.1
  let S := coarsePoints n j I θ i
  have hS := fun p (hp : p∈S) => hI p (coarsePoints_subset n j I θ i hp)
  have hSc := fun p (hp : p∈S) => CoarseWindows.coarsePoints_cap n j I θ K L ρ hcap i p hp
  have havg := hden K L hK0 hL n j i hPR hRP hsK ρ hρ hρ1 S hS hSc m a ha
  have hs := (havg (samePairs S) (samePairs_subset S)).2 (fun p hp => (Finset.mem_filter.mp hp).2)
  have hx := (havg (crossPairs n S θ) (crossPairs_subset n S θ)).1
  have hs' : ‖EnvelopeEnergies.envelopePairAverage n j i
      (fun y => EnvelopeEnergies.localizedPair K L χ a (samePairs S) (FourierTransport.rotatedPhysical ρ y)) m‖ ≤
      C*CircleDivisor.ScaleBounds.D K L (scale j) := hs
  have hx' : ‖EnvelopeEnergies.envelopePairAverage n j i
      (fun y => EnvelopeEnergies.localizedPair K L χ a (crossPairs n S θ) (FourierTransport.rotatedPhysical ρ y)) m‖ ≤
      C*CircleDivisor.ScaleBounds.M K L (scale j) := hx
  rw [CoarseEnergy.same_average] at hs'
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sameMass_nonneg n j I θ _ i m)] at hs'
  constructor
  · exact hs'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (CircleDivisor.ScaleBounds.D_pos hK0 hL0 (scale_pos j)).le)
  · rw [CoarseEnergy.cross_difference n j I θ K L c hK hL0 hc χ hχ a ha
      (FourierTransport.rotatedPhysical ρ) f hsharp i m]
    exact (Complex.abs_re_le_norm _).trans (hx'.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (CircleDivisor.ScaleBounds.M_pos hK0 hL0 (scale_pos j)).le))

end
end CircleDivisor.EnergyV3.DensityTransfer
