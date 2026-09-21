import CircleDivisor.EnergyV3.SameRayCount
import CircleDivisor.EnergyV3.PairEnergies

namespace CircleDivisor.EnergyV3.PairEnergies
open Finset MeasureTheory
open scoped FourierTransform
noncomputable section

structure SameWindow (K L V : ℝ) (P : Finset Pair) : Prop where
  range : ∀ p ∈ P, (p.1.1 : ℝ) ∈ Set.Ico K (2 * K) ∧
    (p.2.1 : ℝ) ∈ Set.Ico K (2 * K) ∧
    (p.1.2 : ℝ) ∈ Set.Ico L (2 * L) ∧ (p.2.2 : ℝ) ∈ Set.Ico L (2 * L)
  same : ∀ p ∈ P, p.1.1 = p.2.1
  coarse : ∀ p ∈ P, ∀ r ∈ P, |((p.1.1 - r.1.1 : ℤ) : ℝ)| ≤ V

theorem SameWindow.admissible {K L V : ℝ} {P : Finset Pair}
    (h : SameWindow K L V P) (pr : Pair × Pair)
    (hpr : pr ∈ FourierEnergy.balancedQuadruples P Prod.fst Prod.snd) :
    SameRayCount.RealAdmissible K L V (encode pr) := by
  obtain ⟨hpr, hb⟩ := mem_filter.mp hpr
  obtain ⟨hp, hr⟩ := mem_product.mp hpr
  rcases hb with ⟨h1, h2⟩
  refine ⟨(h.range pr.2 hr).1, (h.range pr.1 hp).2.2.1,
    (h.range pr.1 hp).2.2.2, (h.range pr.2 hr).2.2.2, ?_, ?_,
    h.same pr.1 hp, (h.same pr.2 hr).symm, h.coarse pr.1 hp pr.2 hr⟩
  · dsimp [PairedCount.firstEquation, encode]; omega
  · dsimp [PairedCount.secondEquation, encode]; omega

theorem balanced_same_count_family {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (hdisj : (T : Set ι).PairwiseDisjoint P)
    (K L V : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hP : ∀ i ∈ T, SameWindow K L V (P i)) :
    (∑ i ∈ T, ((FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd).card : ℝ)) ≤
      48 * (K * V * L ^ 2 + K * L ^ 3) := by
  classical
  let S := T.biUnion (fun i => FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd)
  have hcount := SameRayCount.count_real K L V hK hL hV (S.image encode) (by
    intro x hx
    obtain ⟨pr, hpr, rfl⟩ := mem_image.mp hx
    obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hpr
    exact (hP i hi).admissible pr hpi)
  rw [card_image_of_injective _ encode_injective] at hcount
  have hc : S.card = ∑ i ∈ T, (FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd).card :=
    card_biUnion (balanced_disjoint T P hdisj)
  simpa only [hc, Nat.cast_sum] using hcount

theorem torus_same_energy_family {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (hdisj : (T : Set ι).PairwiseDisjoint P)
    (K L V : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hP : ∀ i ∈ T, SameWindow K L V (P i))
    (b : ι → Pair → ℂ) (hb : ∀ i ∈ T, ∀ p ∈ P i, ‖b i p‖ ≤ 1) :
    (∑ i ∈ T, ∫ u, ‖TorusProjection.polynomial (P i) difference (b i) u‖ ^ 2 ∂TorusProjection.haar) ≤
      48 * (K * V * L ^ 2 + K * L ^ 3) := by
  apply le_trans (sum_le_sum (fun i hi => ?_))
    (balanced_same_count_family T P hdisj K L V hK hL hV hP)
  simpa only [matchingPairs_eq_balanced] using
    TorusProjection.weighted_projection_bound (P i) difference (b i) (hb i hi)

/-- Every normalized localized energy is integrable, and a disjoint family
obeys the exact sum-of-counts bound before either arithmetic estimate. -/
theorem localized_energy_family_le_counts {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    let f := FourierLocalization.localizedAtoms (FourierLocalization.dilate (K * L) χ)
      (fun p : Point => FourierLocalization.coneFrequency K L p.1 p.2)
    (∀ i ∈ T, Integrable (fun x => ‖FourierEnergy.pairSum (P i) (FourierEnergy.weightedAtoms a f) x‖ ^ 2)) ∧
    (∑ i ∈ T, (∫ x, ‖FourierEnergy.pairSum (P i) (FourierEnergy.weightedAtoms a f) x‖ ^ 2) /
      (K * L) ^ 3) ≤ (∫ x, ‖χ x‖ ^ 4) *
        ∑ i ∈ T, ((FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd).card : ℝ) := by
  dsimp only
  have hh i := FourierLocalization.integral_scaled_pairSum_norm_sq_le_balanced_card
    K L c hK hL hc Prod.fst Prod.snd χ hχ (P i) a ha
  refine ⟨fun i hi => (hh i).1, ?_⟩
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  apply (div_le_iff₀ (by positivity : 0 < (K * L) ^ 3)).mpr
  calc
    _ ≤ _ := (hh i).2
    _ = _ := by ring

theorem localized_same_energy_family {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (hdisj : (T : Set ι).PairwiseDisjoint P)
    (K L V c : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hV : 1 ≤ V) (hc : 4 * c ≤ 1)
    (hP : ∀ i ∈ T, SameWindow K L V (P i))
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    let f := FourierLocalization.localizedAtoms (FourierLocalization.dilate (K * L) χ)
      (fun p : Point => FourierLocalization.coneFrequency K L p.1 p.2)
    (∑ i ∈ T, (∫ x, ‖FourierEnergy.pairSum (P i) (FourierEnergy.weightedAtoms a f) x‖ ^ 2) /
      (K * L) ^ 3) ≤ (∫ x, ‖χ x‖ ^ 4) * (48 * (K * V * L ^ 2 + K * L ^ 3)) := by
  apply (localized_energy_family_le_counts T P K L c hK (by linarith) hc χ hχ a ha).2.trans
  exact mul_le_mul_of_nonneg_left (balanced_same_count_family T P hdisj K L V hK hL hV hP)
    (integral_nonneg (fun x => by positivity))

theorem localized_cross_energy_family {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (hdisj : (T : Set ι).PairwiseDisjoint P)
    (K L W V A c : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V) (hA : 1 ≤ A) (hWK : W ≤ A * K) (hc : 4 * c ≤ 1)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate ε C)
    (hP : ∀ i ∈ T, CrossWindow K L W V (P i))
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    let f := FourierLocalization.localizedAtoms (FourierLocalization.dilate (K * L) χ)
      (fun p : Point => FourierLocalization.coneFrequency K L p.1 p.2)
    (∑ i ∈ T, (∫ x, ‖FourierEnergy.pairSum (P i) (FourierEnergy.weightedAtoms a f) x‖ ^ 2) /
      (K * L) ^ 3) ≤ (∫ x, ‖χ x‖ ^ 4) *
        ((576 * (1 + 2 * C * (16 * A) ^ ε)) *
          (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L)) := by
  apply (localized_energy_family_le_counts T P K L c hK (by linarith) hc χ hχ a ha).2.trans
  exact mul_le_mul_of_nonneg_left
    (balanced_cross_count_family T P hdisj K L W V A hK hL hW hV hA hWK ε C hε hC hdiv hP)
    (integral_nonneg (fun x => by positivity))

end
end CircleDivisor.EnergyV3.PairEnergies
