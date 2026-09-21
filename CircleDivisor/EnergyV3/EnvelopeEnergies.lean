import CircleDivisor.EnergyV3.WeightMass
import CircleDivisor.EnergyV3.SameRayEnergies
import CircleDivisor.EnergyV3.LinearTransport

/-! Actual countable envelope energies from localized pair polynomials.
The only hypotheses concern the finite relations and the common cutoff;
no energy bound or averaging inequality is assumed. -/

namespace CircleDivisor.EnergyV3.EnvelopeEnergies
noncomputable section
open MeasureTheory GuthMaldague FourierLocalization FourierEnergy
open scoped FourierTransform ComplexConjugate BigOperators
open PairEnergies
abbrev Space := GuthMaldague.Space

def overlapBound : ℝ := (4 * WeightOverlap.overlapConstant) ^ 3 / weightNormalization

theorem overlapBound_nonneg : 0 ≤ overlapBound := by
  exact div_nonneg (pow_nonneg (mul_nonneg (by norm_num) WeightOverlap.overlapConstant_nonneg) _)
    weightNormalization_pos.le

def localizedPair (K L : ℝ) (χ : SchwartzMap FourierLocalization.Space ℂ)
    (a : Point → ℂ) (P : Finset Pair) : FourierLocalization.Space → ℂ :=
  pairSum P (weightedAtoms a (localizedAtoms (dilate (K * L) χ)
    (fun p : Point => coneFrequency K L p.1 p.2)))

theorem localizedPair_continuous (K L : ℝ) (χ : SchwartzMap FourierLocalization.Space ℂ)
    (a : Point → ℂ) (P : Finset Pair) : Continuous (localizedPair K L χ a P) := by
  unfold localizedPair pairSum pairValue weightedAtoms localizedAtoms dilate
  apply continuous_finsetSum
  intro p hp
  exact (continuous_const.mul ((χ.continuous.comp (continuous_const_smul _)).mul
    (continuous_character _))).mul
      ((continuous_const.mul ((χ.continuous.comp (continuous_const_smul _)).mul
        (continuous_character _))).star)

theorem localizedPair_memLp (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : Finset Pair) :
    MemLp (localizedPair K L χ a P) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (localizedPair_continuous K L χ a P).aestronglyMeasurable).2
  exact (integral_scaled_pairSum_norm_sq_le_balanced_card K L c hK hL hc
    Prod.fst Prod.snd χ hχ P a ha).1

def envelopePairAverage (n j : ℕ) (i : CapIndex j) (g : Space → ℂ) (m : Lattice) : ℂ :=
  CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m) g

theorem pair_average_energy (n j : ℕ) (i : CapIndex j)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : Finset Pair) :
    Summable (fun m : Lattice => envelopeVolume n j i m *
      ‖envelopePairAverage n j i (localizedPair K L χ a P) m‖ ^ 2) ∧
    (∑' m : Lattice, envelopeVolume n j i m *
      ‖envelopePairAverage n j i (localizedPair K L χ a P) m‖ ^ 2) ≤
        overlapBound * ∫ x, ‖localizedPair K L χ a P x‖ ^ 2 := by
  exact (WeightMass.actual_countable_averaging n j i _
    (localizedPair_memLp K L c hK hL hc χ hχ a ha P)).2

theorem family_average_energy (n j : ℕ) (P : CapIndex j → Finset Pair)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    (∑ i : CapIndex j, (∑' m : Lattice, envelopeVolume n j i m *
      ‖envelopePairAverage n j i (localizedPair K L χ a (P i)) m‖ ^ 2) / (K * L) ^ 3) ≤
        overlapBound * ∑ i : CapIndex j, (∫ x, ‖localizedPair K L χ a (P i) x‖ ^ 2) / (K * L) ^ 3 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hh := (pair_average_energy n j i K L c hK hL hc χ hχ a ha (P i)).2
  have hd := div_le_div_of_nonneg_right hh (show 0 ≤ (K * L) ^ 3 by positivity)
  convert hd using 1 <;> ring

theorem transported_pair_average_energy (n j : ℕ) (i : CapIndex j) (e : Space ≃L[ℝ] Space)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : Finset Pair) :
    Summable (fun m : Lattice => envelopeVolume n j i m *
      ‖envelopePairAverage n j i (fun y => localizedPair K L χ a P (e y)) m‖ ^ 2) ∧
    (∑' m : Lattice, envelopeVolume n j i m *
      ‖envelopePairAverage n j i (fun y => localizedPair K L χ a P (e y)) m‖ ^ 2) ≤
        (overlapBound * LinearTransport.jacobian e) * ∫ x, ‖localizedPair K L χ a P x‖ ^ 2 := by
  have hh := (WeightMass.actual_countable_averaging n j i _
    (LinearTransport.memLp_comp e (localizedPair_memLp K L c hK hL hc χ hχ a ha P))).2
  refine ⟨hh.1, ?_⟩
  have he := LinearTransport.integral_comp e (fun x => ‖localizedPair K L χ a P x‖ ^ 2)
  simpa only [he, mul_assoc, overlapBound, envelopePairAverage] using hh.2

theorem transported_family_average_energy (n j : ℕ) (P : CapIndex j → Finset Pair)
    (e : Space ≃L[ℝ] Space) (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    (∑ i : CapIndex j, (∑' m : Lattice, envelopeVolume n j i m *
      ‖envelopePairAverage n j i (fun y => localizedPair K L χ a (P i) (e y)) m‖ ^ 2) / (K * L) ^ 3) ≤
        (overlapBound * LinearTransport.jacobian e) *
          ∑ i : CapIndex j, (∫ x, ‖localizedPair K L χ a (P i) x‖ ^ 2) / (K * L) ^ 3 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hh := (transported_pair_average_energy n j i e K L c hK hL hc χ hχ a ha (P i)).2
  have hd := div_le_div_of_nonneg_right hh (show 0 ≤ (K * L) ^ 3 by positivity)
  convert hd using 1 <;> ring

theorem finite_first_mass (n j : ℕ) (i : CapIndex j) (I : Finset Lattice)
    (g : Space → ℝ) (hg : Integrable g) (hnn : ∀ x, 0 ≤ g x) :
    ∑ m ∈ I, (∫ x, g x * envelopeWeight n j i m x) ≤ overlapBound * ∫ x, g x := by
  have hwB (m : Lattice) (x : Space) : envelopeWeight n j i m x ≤ overlapBound := by
    simpa only [Finset.sum_singleton, overlapBound] using WeightOverlap.actual_envelope_finite_overlap n j i {m} x
  have hwcont (m : Lattice) : Continuous (envelopeWeight n j i m) := by
    unfold envelopeWeight normalizedWeight
    apply Continuous.div_const
    exact baseWeight_continuous.comp
      ((WeightMass.coordinateEquiv (radius n) (scale j) (leftEndpoint j i)
        (radius_pos n).ne' (scale_pos j).ne').continuous.comp (continuous_id.sub continuous_const))
  have hi (m : Lattice) : Integrable (fun x => g x * envelopeWeight n j i m x) :=
    hg.mul_bdd (hwcont m).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_of_nonneg (envelopeWeight_nonneg n j i m x)] using hwB m x))
  rw [← integral_finsetSum I (fun m _ => hi m), ← integral_const_mul]
  apply integral_mono (integrable_finsetSum I (fun m _ => hi m)) (hg.const_mul overlapBound)
  intro x
  dsimp only
  rw [← Finset.mul_sum, mul_comm overlapBound]
  exact mul_le_mul_of_nonneg_left (WeightOverlap.actual_envelope_finite_overlap n j i I x) (hnn x)

theorem countable_first_mass (n j : ℕ) (i : CapIndex j)
    (g : Space → ℝ) (hg : Integrable g) (hnn : ∀ x, 0 ≤ g x) :
    Summable (fun m : Lattice => ∫ x, g x * envelopeWeight n j i m x) ∧
    (∑' m : Lattice, ∫ x, g x * envelopeWeight n j i m x) ≤ overlapBound * ∫ x, g x := by
  have hnonneg : 0 ≤ (fun m : Lattice => ∫ x, g x * envelopeWeight n j i m x) :=
    fun m => integral_nonneg (fun x => mul_nonneg (hnn x) (envelopeWeight_nonneg n j i m x))
  exact ⟨summable_of_sum_le hnonneg (fun I => finite_first_mass n j i I g hg hnn),
    Real.tsum_le_of_sum_le hnonneg (fun I => finite_first_mass n j i I g hg hnn)⟩

end
end CircleDivisor.EnergyV3.EnvelopeEnergies
