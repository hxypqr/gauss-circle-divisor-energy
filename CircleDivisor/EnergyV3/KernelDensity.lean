import CircleDivisor.EnergyV3.KernelEnvelope
import CircleDivisor.EnergyV3.DensitySums
import CircleDivisor.EnergyV3.EnvelopeEnergies

/-! Actual weighted quadratic integrals reduce to finite Fourier-kernel sums.
The bounds here are internal composition lemmas, not external inputs. -/
namespace CircleDivisor.EnergyV3.KernelDensity
noncomputable section
open MeasureTheory GuthMaldague FourierLocalization FourierEnergy
open scoped FourierTransform ComplexConjugate BigOperators
abbrev Space := GuthMaldague.Space

theorem envelopeKernel_integrable (χ : SchwartzMap Space ℂ) (P : ℝ)
    (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    Integrable (KernelEnvelope.envelopeKernel χ P n j i m) := by
  have hw := WeightMass.envelopeWeight_integrable n j i m
  have hχ : Continuous (fun z : Space => (‖χ (P⁻¹ • z)‖^2 : ℝ)) := by fun_prop
  apply (hw.const_mul ((SchwartzMap.seminorm ℝ 0 0 χ)^2)).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hχ.aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable))
  filter_upwards with z
  change ‖((‖χ (P⁻¹ • z)‖^2 : ℝ) : ℂ)*(envelopeWeight n j i m z : ℂ)‖ ≤
    SchwartzMap.seminorm ℝ 0 0 χ ^ 2 * envelopeWeight n j i m z
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖χ (P⁻¹ • z)‖),
    Real.norm_of_nonneg (envelopeWeight_nonneg n j i m z)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℝ χ _) 2)
    (envelopeWeight_nonneg n j i m z)

theorem weighted_localized_pairValue {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (a : ι → ℂ) (w : Space → ℝ) (p : ι × ι) (z : Space) :
    (w z : ℂ)*pairValue (weightedAtoms a (localizedAtoms χ ξ)) p z =
      pairCoefficient a p * ((secondWeight χ z * (w z : ℂ))*character (ξ p.1-ξ p.2) z) := by
  have hh := localized_pairValue χ ξ p z
  simp only [pairValue, weightedAtoms, pairCoefficient, map_mul] at hh ⊢
  calc
    _ = (a p.1 * conj (a p.2)) * (w z : ℂ) *
        (localizedAtoms χ ξ p.1 z * conj (localizedAtoms χ ξ p.2 z)) := by ring
    _ = _ := by rw [hh]; ring

theorem integral_weighted_pairSum {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (a : ι → ℂ) (w : Space → ℝ) (F : Finset (ι × ι))
    (hk : Integrable (fun z => secondWeight χ z * (w z : ℂ))) :
    (∫ z, (w z : ℂ) * pairSum F (weightedAtoms a (localizedAtoms χ ξ)) z) =
      ∑ p ∈ F, pairCoefficient a p * 𝓕 (fun z => secondWeight χ z * (w z : ℂ)) (ξ p.2-ξ p.1) := by
  simp only [pairSum, Finset.mul_sum, weighted_localized_pairValue]
  rw [integral_finsetSum F]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_const_mul, integral_weighted_character, neg_sub]
  · intro p hp
    exact (integrable_weighted_character hk _).const_mul _

theorem norm_average_pairSum_le {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (a : ι → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (w : Space → ℝ) (F : Finset (ι × ι))
    (hk : Integrable (fun z => secondWeight χ z * (w z : ℂ)))
    (V B : ℝ) (hV : 0 < V) (d : (ι × ι) → ℝ)
    (hb : ∀ p ∈ F, ‖𝓕 (fun z => secondWeight χ z * (w z : ℂ)) (ξ p.2-ξ p.1)‖ ≤ V*B*d p) :
    ‖CountableAveraging.average volume w V (pairSum F (weightedAtoms a (localizedAtoms χ ξ)))‖ ≤
      B * ∑ p ∈ F, d p := by
  unfold CountableAveraging.average
  rw [integral_weighted_pairSum χ ξ a w F hk, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hV.le]
  have hh : ‖∑ p ∈ F, pairCoefficient a p *
      𝓕 (fun z => secondWeight χ z * (w z : ℂ)) (ξ p.2-ξ p.1)‖ ≤ V*B*∑ p ∈ F, d p := by
    calc
      _ ≤ ∑ p ∈ F, ‖pairCoefficient a p *
          𝓕 (fun z => secondWeight χ z * (w z : ℂ)) (ξ p.2-ξ p.1)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ F, V*B*d p := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (pairCoefficient_norm_le_one a ha p)).trans (hb p hp)
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ V⁻¹*(V*B*∑ p ∈ F, d p) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hV.le)
    _ = _ := by field_simp

theorem actual_envelope_average_le {ι : Type*} (χ : SchwartzMap Space ℂ) (P : ℝ)
    (n j : ℕ) (i : CapIndex j) (m : Lattice) (ξ : ι → Space)
    (a : ι → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (F : Finset (ι × ι)) (B : ℝ) (d : (ι × ι) → ℝ)
    (hb : ∀ p ∈ F, ‖𝓕 (KernelEnvelope.envelopeKernel χ P n j i m) (ξ p.2-ξ p.1)‖ ≤
      envelopeVolume n j i m * B * d p) :
    ‖CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
      (pairSum F (weightedAtoms a (localizedAtoms (dilate P χ) ξ)))‖ ≤ B*∑ p ∈ F, d p := by
  exact norm_average_pairSum_le _ ξ a ha _ F (envelopeKernel_integrable χ P n j i m)
    _ B (WeightMass.envelopeVolume_pos n j i m) d hb

theorem transportedEnvelopeKernel_integrable (χ : SchwartzMap Space ℂ) (P : ℝ)
    (E : Space →L[ℝ] Space) (n j : ℕ) (i : CapIndex j) (m : Lattice) :
    Integrable (KernelEnvelope.transportedEnvelopeKernel χ P E n j i m) := by
  have hw := WeightMass.envelopeWeight_integrable n j i m
  have hχ : Continuous (fun z : Space => (‖χ (P⁻¹ • E z)‖^2 : ℝ)) := by fun_prop
  apply (hw.const_mul ((SchwartzMap.seminorm ℝ 0 0 χ)^2)).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hχ.aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable))
  filter_upwards with z
  change ‖((‖χ (P⁻¹ • E z)‖^2 : ℝ) : ℂ)*(envelopeWeight n j i m z : ℂ)‖ ≤
    SchwartzMap.seminorm ℝ 0 0 χ ^ 2 * envelopeWeight n j i m z
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖χ (P⁻¹ • E z)‖),
    Real.norm_of_nonneg (envelopeWeight_nonneg n j i m z)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℝ χ _) 2)
    (envelopeWeight_nonneg n j i m z)

theorem decay_comparison (d r J : ℝ) (hd : 0≤d) (hr : 0≤r) (hJ : 1≤J) (h : d≤J*r) :
    ((1+r)^8)⁻¹ ≤ J^8*((1+d)^8)⁻¹ := by
  have hJ0 : 0<J := by linarith
  have hb : 1+d ≤ J*(1+r) := by nlinarith
  calc
    _ = J^8/(J*(1+r))^8 := by field_simp
    _ ≤ J^8/(1+d)^8 := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by positivity) hb 8)
    _ = _ := by rw [div_eq_mul_inv]

/-- Uniform kernel-to-average estimate for any finite pair relation and any
bounded physical map. The only metric premise is a concrete matrix inequality. -/
theorem uniform_transported_average (χ : SchwartzMap Space ℂ) (C₀ J : ℝ)
    (hC₀ : 0≤C₀) (hJ : 1≤J) : ∃ B : ℝ, 0<B ∧
      ∀ P : ℝ, 0<P → ∀ E : Space →L[ℝ] Space, ‖E‖≤C₀ →
      ∀ n j : ℕ, ∀ i : CapIndex j, radius n<4*P → ∀ m : Lattice,
      ∀ (ξ : DensitySums.Point → Space) (a : DensitySums.Point → ℂ), (∀ p, ‖a p‖≤1) →
      ∀ F : Finset (DensitySums.Point × DensitySums.Point), ∀ d : (DensitySums.Point × DensitySums.Point) → ℝ,
        (∀ p∈F, 0≤d p) →
        (∀ p∈F, d p ≤ J*‖(KernelEnvelope.synthesisEquiv n j i : Space →L[ℝ] Space).adjoint
          (ξ p.2-ξ p.1)‖) →
        ‖CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
          (pairSum F (weightedAtoms a (localizedAtoms (fun z => χ (P⁻¹ • E z)) ξ)))‖ ≤
            B*∑ p∈F, ((1+d p)^8)⁻¹ := by
  obtain ⟨D,hD,hkernel⟩ := KernelEnvelope.transported_envelope_kernel_decay χ C₀ 8 hC₀ (by norm_num)
  refine ⟨D*J^8,by positivity,?_⟩
  intro P hP E hE n j i hR m ξ a ha F d hd hmetric
  apply norm_average_pairSum_le _ ξ a ha _ F
    (transportedEnvelopeKernel_integrable χ P E n j i m) _ _
    (WeightMass.envelopeVolume_pos n j i m) (fun p => ((1+d p)^8)⁻¹)
  intro p hp
  have hV := WeightMass.envelopeVolume_pos n j i m
  have hk := hkernel P hP E hE n j i hR m (ξ p.2-ξ p.1)
  norm_num only [Real.rpow_neg (by positivity : 0 ≤ 1+‖(KernelEnvelope.synthesisEquiv n j i : Space →L[ℝ] Space).adjoint (ξ p.2-ξ p.1)‖),
    Real.rpow_natCast, Real.rpow_ofNat] at hk
  have hc := decay_comparison (d p) _ J (hd p hp) (norm_nonneg _) hJ (hmetric p hp)
  calc
    _ ≤ _ := hk
    _ ≤ D*envelopeVolume n j i m*(J^8*((1+d p)^8)⁻¹) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end
end CircleDivisor.EnergyV3.KernelDensity
