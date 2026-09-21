import CircleDivisor.EnergyV3.PairedCountReal
import CircleDivisor.EnergyV3.TorusProjection
import CircleDivisor.FourierLocalization

/-! Exact finite pair relations connect the two-width count both to the Haar
energy in §2 and to the actual scaled Schwartz-localized energy in §3. -/
namespace CircleDivisor.EnergyV3.PairEnergies
open Finset MeasureTheory
open scoped ComplexConjugate FourierTransform
noncomputable section

abbrev Point := ℤ × ℤ
abbrev Pair := Point × Point
def projection (p : Point) : TorusProjection.Frequency := (p.2, p.1 * p.2)
def difference (p : Pair) : TorusProjection.Frequency := projection p.1 - projection p.2

theorem projection_injective {S : Finset Point} (hS : ∀ p ∈ S, p.2 ≠ 0) :
    Set.InjOn projection (S : Set Point) := by
  intro p hp q hq heq
  have h := Prod.mk.inj heq
  have hk : p.1 = q.1 := mul_right_cancel₀ (hS p hp) (by simpa [projection, ← h.1] using h.2)
  exact Prod.ext hk h.1

def pairCoefficient (a : Point → ℂ) (ω : Point → ℝ) (t : ℝ) (p : Pair) : ℂ :=
  a p.1 * conj (a p.2) * Complex.exp ((2 * Real.pi * t * (ω p.1 - ω p.2) : ℝ) * Complex.I)

theorem pairCoefficient_norm_le (a : Point → ℂ) (ω : Point → ℝ) (t : ℝ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (p : Pair) : ‖pairCoefficient a ω t p‖ ≤ 1 := by
  simp only [pairCoefficient, norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one]
  nlinarith [ha p.1, ha p.2, norm_nonneg (a p.1), norm_nonneg (a p.2)]

def encode (pr : Pair × Pair) : PairedCount.Quadruple :=
  ⟨pr.1.1.1, pr.1.2.1, pr.2.2.1, pr.2.1.1,
    pr.1.1.2, pr.1.2.2, pr.2.2.2, pr.2.1.2⟩

theorem encode_injective : Function.Injective encode := by
  rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩ ⟨⟨⟨a',b'⟩,⟨c',d'⟩⟩,⟨⟨e',f'⟩,⟨g',h'⟩⟩⟩ heq
  simp only [encode, SpacingCount.Quadruple.mk.injEq] at heq
  simp_all

theorem balance_iff_difference (p r : Pair) :
    FourierEnergy.frequencyBalance Prod.fst Prod.snd p r ↔ difference p = difference r := by
  simp [FourierEnergy.frequencyBalance, difference, projection, Prod.ext_iff]

structure CrossWindow (K L W V : ℝ) (P : Finset Pair) : Prop where
  range : ∀ p ∈ P, (p.1.1 : ℝ) ∈ Set.Ico K (2 * K) ∧
    (p.2.1 : ℝ) ∈ Set.Ico K (2 * K) ∧
    (p.1.2 : ℝ) ∈ Set.Ico L (2 * L) ∧ (p.2.2 : ℝ) ∈ Set.Ico L (2 * L)
  cross : ∀ p ∈ P, p.1.1 ≠ p.2.1
  width : ∀ p ∈ P, |((p.1.1 - p.2.1 : ℤ) : ℝ)| ≤ W
  coarse : ∀ p ∈ P, ∀ r ∈ P, |((p.2.1 - r.1.1 : ℤ) : ℝ)| ≤ V

theorem CrossWindow.admissible {K L W V : ℝ} {P : Finset Pair}
    (h : CrossWindow K L W V P) (pr : Pair × Pair)
    (hpr : pr ∈ FourierEnergy.balancedQuadruples P Prod.fst Prod.snd) :
    PairedCount.RealAdmissible K L W V (encode pr) := by
  obtain ⟨hpr, hb⟩ := mem_filter.mp hpr
  obtain ⟨hp, hr⟩ := mem_product.mp hpr
  rcases hb with ⟨h1, h2⟩
  refine ⟨(h.range pr.2 hr).1, (h.range pr.1 hp).2.2.1,
    (h.range pr.1 hp).2.2.2, (h.range pr.2 hr).2.2.2, ?_, ?_,
    h.width pr.1 hp, ?_, h.coarse pr.1 hp pr.2 hr, h.cross pr.1 hp,
    Ne.symm (h.cross pr.2 hr)⟩
  · dsimp [PairedCount.firstEquation, encode]
    omega
  · dsimp [PairedCount.secondEquation, encode]
    omega
  · simpa only [encode, Int.cast_sub, abs_sub_comm] using h.width pr.2 hr

theorem balanced_cross_count (K L W V A : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V) (hA : 1 ≤ A) (hWK : W ≤ A * K)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate ε C)
    (P : Finset Pair) (hP : CrossWindow K L W V P) :
    ((FourierEnergy.balancedQuadruples P Prod.fst Prod.snd).card : ℝ) ≤
      (576 * (1 + 2 * C * (16 * A) ^ ε)) *
        (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L) := by
  have hh := PairedCount.paired_count_real K L W V A hK hL hW hV hA hWK
    ε C hε hC hdiv ((FourierEnergy.balancedQuadruples P Prod.fst Prod.snd).image encode)
    (by intro x hx; obtain ⟨pr, hpr, rfl⟩ := mem_image.mp hx; exact hP.admissible pr hpr)
  simpa only [card_image_of_injective _ encode_injective] using hh

theorem matchingPairs_eq_balanced (P : Finset Pair) :
    TorusProjection.matchingPairs P difference = FourierEnergy.balancedQuadruples P Prod.fst Prod.snd := by
  ext pr
  simp [TorusProjection.matchingPairs, FourierEnergy.balancedQuadruples, balance_iff_difference]

theorem torus_cross_energy (K L W V A : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V) (hA : 1 ≤ A) (hWK : W ≤ A * K)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate ε C)
    (P : Finset Pair) (hP : CrossWindow K L W V P)
    (b : Pair → ℂ) (hb : ∀ p ∈ P, ‖b p‖ ≤ 1) :
    (∫ u, ‖TorusProjection.polynomial P difference b u‖ ^ 2 ∂TorusProjection.haar) ≤
      (576 * (1 + 2 * C * (16 * A) ^ ε)) *
        (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L) := by
  have hh := TorusProjection.weighted_projection_bound P difference b hb
  rw [matchingPairs_eq_balanced] at hh
  exact hh.trans (balanced_cross_count K L W V A hK hL hW hV hA hWK ε C hε hC hdiv P hP)

theorem localized_cross_energy (K L W V A c : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V) (hA : 1 ≤ A) (hWK : W ≤ A * K) (hc : 4 * c ≤ 1)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate ε C)
    (P : Finset Pair) (hP : CrossWindow K L W V P)
    (χ : SchwartzMap FourierLocalization.Space ℂ)
    (hχ : Function.support (𝓕 (χ : FourierLocalization.Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    let f := FourierLocalization.localizedAtoms (FourierLocalization.dilate (K * L) χ)
      (fun p : Point => FourierLocalization.coneFrequency K L p.1 p.2)
    Integrable (fun x => ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) ∧
    (∫ x, ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) /
      (K * L) ^ 3 ≤ (∫ x, ‖χ x‖ ^ 4) *
        ((576 * (1 + 2 * C * (16 * A) ^ ε)) *
          (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L)) := by
  have hh := FourierLocalization.integral_scaled_pairSum_norm_sq_le_balanced_card
    K L c hK (by linarith) hc Prod.fst Prod.snd χ hχ P a ha
  refine ⟨hh.1, (div_le_iff₀ (by positivity : 0 < (K * L) ^ 3)).mpr ?_⟩
  calc
    _ ≤ (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 4) *
        (FourierEnergy.balancedQuadruples P Prod.fst Prod.snd).card := hh.2
    _ ≤ (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 4) *
        ((576 * (1 + 2 * C * (16 * A) ^ ε)) *
          (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L)) := by
      gcongr
      exact balanced_cross_count K L W V A hK hL hW hV hA hWK ε C hε hC hdiv P hP
    _ = _ := by ring

theorem balanced_disjoint {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (hP : (T : Set ι).PairwiseDisjoint P) :
    (T : Set ι).PairwiseDisjoint (fun i => FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro pr hp hr
  exact disjoint_left.mp (hP hi hj hij)
    (mem_product.mp (mem_filter.mp hp).1).1 (mem_product.mp (mem_filter.mp hr).1).1

/-- The sum over disjoint coarse windows has no factor counting those windows. -/
theorem balanced_cross_count_family {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (hdisj : (T : Set ι).PairwiseDisjoint P)
    (K L W V A : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V) (hA : 1 ≤ A) (hWK : W ≤ A * K)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate ε C)
    (hP : ∀ i ∈ T, CrossWindow K L W V (P i)) :
    (∑ i ∈ T, ((FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd).card : ℝ)) ≤
      (576 * (1 + 2 * C * (16 * A) ^ ε)) *
        (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L) := by
  classical
  let S := T.biUnion (fun i => FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd)
  have hcount := PairedCount.paired_count_real K L W V A hK hL hW hV hA hWK
    ε C hε hC hdiv (S.image encode) (by
      intro x hx
      obtain ⟨pr, hpr, rfl⟩ := mem_image.mp hx
      obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hpr
      exact (hP i hi).admissible pr hpi)
  rw [card_image_of_injective _ encode_injective] at hcount
  have hc : S.card = ∑ i ∈ T, (FourierEnergy.balancedQuadruples (P i) Prod.fst Prod.snd).card :=
    card_biUnion (balanced_disjoint T P hdisj)
  simpa only [hc, Nat.cast_sum] using hcount

theorem torus_cross_energy_family {ι : Type*} (T : Finset ι) (P : ι → Finset Pair)
    (hdisj : (T : Set ι).PairwiseDisjoint P)
    (K L W V A : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hV : 1 ≤ V) (hA : 1 ≤ A) (hWK : W ≤ A * K)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate ε C)
    (hP : ∀ i ∈ T, CrossWindow K L W V (P i))
    (b : ι → Pair → ℂ) (hb : ∀ i ∈ T, ∀ p ∈ P i, ‖b i p‖ ≤ 1) :
    (∑ i ∈ T, ∫ u, ‖TorusProjection.polynomial (P i) difference (b i) u‖ ^ 2 ∂TorusProjection.haar) ≤
      (576 * (1 + 2 * C * (16 * A) ^ ε)) *
        (K * L) ^ ε * K * (W ^ 2 * L ^ 2 + V * W * L) := by
  apply le_trans (sum_le_sum (fun i hi => ?_))
    (balanced_cross_count_family T P hdisj K L W V A hK hL hW hV hA hWK ε C hε hC hdiv hP)
  simpa only [matchingPairs_eq_balanced] using
    TorusProjection.weighted_projection_bound (P i) difference (b i) (hb i hi)

end
end CircleDivisor.EnergyV3.PairEnergies
