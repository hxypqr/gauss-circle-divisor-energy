import CircleDivisor.EnergyV3.MetricTransport
import CircleDivisor.EnergyV3.KernelDensity
import CircleDivisor.EnergyV3.CanonicalLocalization

namespace CircleDivisor.EnergyV3.LocalDensityActual
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory GuthMaldague FourierLocalization FourierEnergy AngularAtoms
open scoped BigOperators FourierTransform
abbrev Point := DensitySums.Point

def rotatedFrequency (K L ρ : ℝ) (p : Point) : GuthMaldague.Space :=
  rotate ρ (LinearTransport.circularFrequency (coneFrequency K L p.1 p.2))

theorem distance_symm (K L s t : ℝ) (p q : Point) :
    DensitySums.distance K L s t p q = DensitySums.distance K L s t q p := by
  unfold DensitySums.distance AdaptedMetric.dualCoordinates
  rw [show ConeGeometry.frequency K L q.1 q.2-ConeGeometry.frequency K L p.1 p.2 =
    -(ConeGeometry.frequency K L p.1 p.2-ConeGeometry.frequency K L q.1 q.2) by abel]
  rw [Matrix.mulVec_neg, norm_neg]

theorem point_angle_mem (K L ρ : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (j : ℕ) (i : CapIndex j) (p : Point)
    (hp : K ≤ (p.1:ℝ) ∧ (p.1:ℝ) < 2*K ∧ L ≤ (p.2:ℝ))
    (hc : rotatedFrequency K L ρ p ∈ cap j i) :
    rayAngle (Real.sqrt ((p.1:ℝ)/K))+ρ ∈ angularInterval j i := by
  have ht := NeighborCount.sqrt_parameter_bounds hK hp.1 hp.2.1
  have hh := hc.2
  change cylindricalAngle (rotatedFrequency K L ρ p) ∈ angularInterval j i at hh
  unfold rotatedFrequency at hh
  rw [circularFrequency_generator K L hK hL p.1 p.2 hp.1,
    generator_rotated_angle ρ _ _ hρ hρ1 (div_pos (lt_of_lt_of_le hL hp.2.2) hL)
      ht.1 (by nlinarith [ht.2.2])] at hh
  exact hh

theorem actual_cap_center (S : Finset Point) (hS0 : S.Nonempty)
    (K L ρ : ℝ) (hK : 0 < K) (hL : 0 < L) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (j : ℕ) (i : CapIndex j)
    (hS : ∀ p ∈ S, K ≤ (p.1:ℝ) ∧ (p.1:ℝ) < 2*K ∧ L ≤ (p.2:ℝ) ∧ (p.2:ℝ) < 2*L)
    (hc : ∀ p ∈ S, rotatedFrequency K L ρ p ∈ cap j i) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ 2 ∧
      |rayAngle t-(leftEndpoint j i-ρ)| ≤ (2*Real.pi)*scale j ∧
      ∀ p ∈ S, |Real.sqrt ((p.1:ℝ)/K)-t| ≤ (8*Real.pi)*scale j := by
  obtain ⟨p₀, hp₀⟩ := hS0
  let t := Real.sqrt ((p₀.1:ℝ)/K)
  have h₀ := NeighborCount.sqrt_parameter_bounds hK (hS p₀ hp₀).1 (hS p₀ hp₀).2.1
  have ha₀ := point_angle_mem K L ρ hK hL hρ hρ1 j i p₀
    ⟨(hS p₀ hp₀).1,(hS p₀ hp₀).2.1,(hS p₀ hp₀).2.2.1⟩ (hc p₀ hp₀)
  change leftEndpoint j i ≤ rayAngle t+ρ ∧
    rayAngle t+ρ < leftEndpoint j i+2*Real.pi*scale j at ha₀
  refine ⟨t,h₀.1,h₀.2.1,?_,?_⟩
  · rw [abs_le]
    constructor <;> linarith [mul_pos (by positivity : 0<2*Real.pi) (scale_pos j)]
  intro p hp
  have ht := NeighborCount.sqrt_parameter_bounds hK (hS p hp).1 (hS p hp).2.1
  have ha := point_angle_mem K L ρ hK hL hρ hρ1 j i p
    ⟨(hS p hp).1,(hS p hp).2.1,(hS p hp).2.2.1⟩ (hc p hp)
  change leftEndpoint j i ≤ rayAngle (Real.sqrt ((p.1:ℝ)/K))+ρ ∧
    rayAngle (Real.sqrt ((p.1:ℝ)/K))+ρ < leftEndpoint j i+2*Real.pi*scale j at ha
  have hh := parameter_angle_separation (Real.sqrt ((p.1:ℝ)/K)) t ht.1
    (by nlinarith [ht.2.2, (hS p hp).2.1]) h₀.1 (by
      have hh : K*t^2=(p₀.1:ℝ) := h₀.2.2
      nlinarith [(hS p₀ hp₀).2.1])
  have hd : |rayAngle (Real.sqrt ((p.1:ℝ)/K))-rayAngle t| ≤ 2*Real.pi*scale j := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

theorem physicalAtoms_eq (K L ρ : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap GuthMaldague.Space ℂ) :
    CanonicalLocalization.physicalAtom K L ρ χ =
      localizedAtoms (fun z => χ ((K*L)⁻¹ • FourierTransport.rotatedPhysical ρ z))
        (rotatedFrequency K L ρ) := by
  ext p z
  rw [CanonicalLocalization.physicalAtom_eq K L ρ hP χ p z]
  rfl

theorem actual_average_decay (χ : SchwartzMap GuthMaldague.Space ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ K L : ℝ, 0 < K → 0 < L →
      ∀ n j : ℕ, ∀ i : CapIndex j, K*L ≤ radius n → radius n < 4*(K*L) →
      ∀ ρ t : ℝ, 0 < t → |rayAngle t-(leftEndpoint j i-ρ)| ≤ (2*Real.pi)*scale j →
      ∀ m : Lattice, ∀ a : Point → ℂ, (∀ p, ‖a p‖ ≤ 1) → ∀ F : Finset (Point×Point),
        ‖CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
          (pairSum F (weightedAtoms a (CanonicalLocalization.physicalAtom K L ρ χ)))‖ ≤
        B * ∑ p ∈ F, ((1+DensitySums.distance K L (scale j) t p.1 p.2)^8)⁻¹ := by
  obtain ⟨B,hB,havg⟩ := KernelDensity.uniform_transported_average χ 1
    (5*(2*Real.pi+1)^2) (by norm_num) (by nlinarith [Real.pi_pos])
  refine ⟨B,hB,?_⟩
  intro K L hK hL n j i hPR hRP ρ t ht hδ m a ha F
  rw [physicalAtoms_eq K L ρ (mul_pos hK hL).ne' χ]
  have hm (p : Point×Point) (_hp : p∈F) :
      DensitySums.distance K L (scale j) t p.1 p.2 ≤ (5*(2*Real.pi+1)^2)*
        ‖(KernelEnvelope.synthesisEquiv n j i : GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint
          (rotatedFrequency K L ρ p.2-rotatedFrequency K L ρ p.1)‖ := by
    have hh := MetricTransport.canonical_metric_comparison (K*L) (2*Real.pi) ρ t n j i
      (mul_pos hK hL).le hPR ht (by positivity) hδ
      (coneFrequency K L p.2.1 p.2.2-coneFrequency K L p.1.1 p.1.2)
    rw [MetricTransport.circularFrequency_sub, rotate_sub] at hh
    rw [LocalizationNormalization.coneFrequency_eq_frequency K L hK.le,
      LocalizationNormalization.coneFrequency_eq_frequency K L hK.le] at hh
    change DensitySums.distance K L (scale j) t p.2 p.1 ≤ _ at hh
    simpa only [distance_symm K L (scale j) t p.2 p.1, rotatedFrequency,
      LocalizationNormalization.coneFrequency_eq_frequency K L hK.le] using hh
  have hn (p : Point×Point) (_hp : p∈F) : 0 ≤ DensitySums.distance K L (scale j) t p.1 p.2 :=
    norm_nonneg _
  have hh := havg (K*L) (mul_pos hK hL)
    (FourierTransport.rotatedPhysical ρ : GuthMaldague.Space →L[ℝ] GuthMaldague.Space)
    (FourierTransport.rotatedPhysical_contraction ρ) n j i hRP m
    (rotatedFrequency K L ρ) a ha F (fun p => DensitySums.distance K L (scale j) t p.1 p.2) hn hm
  exact hh

def density (K L s : ℝ) : ℝ := s*K*L*(1+1/(K*s^2))*(1+1/(L*s))
def sameDensity (K L s : ℝ) : ℝ := s*K*L*(1+1/(K*s^2))

def crossConstant : ℝ := 162*(256*(64/63))*5832*(8*Real.pi)^2
def sameConstant : ℝ := 162*(256*(64/63))*27*(8*Real.pi)

theorem crossConstant_pos : 0 < crossConstant := by unfold crossConstant; positivity
theorem sameConstant_pos : 0 < sameConstant := by unfold sameConstant; positivity

/-- The actual local-density estimates. `F` can be any subrelation of the
coarse cap, including the distinct-ray relation; the stronger second estimate
applies to the same-ray relation. All constants precede every scale, angle,
coefficient, cap, and translated envelope. -/
theorem actual_local_density (χ : SchwartzMap GuthMaldague.Space ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K L : ℝ, 0 < K → 1 ≤ L →
      ∀ n j : ℕ, ∀ i : CapIndex j, K*L ≤ radius n → radius n < 4*(K*L) →
      1 ≤ scale j*K → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      ∀ S : Finset Point,
      (∀ p ∈ S, K ≤ (p.1:ℝ) ∧ (p.1:ℝ) < 2*K ∧ L ≤ (p.2:ℝ) ∧ (p.2:ℝ) < 2*L) →
      (∀ p ∈ S, rotatedFrequency K L ρ p ∈ cap j i) →
      ∀ m : Lattice, ∀ a : Point → ℂ, (∀ p, ‖a p‖ ≤ 1) →
      ∀ F : Finset (Point×Point), F ⊆ S ×ˢ S →
        (‖CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
          (pairSum F (weightedAtoms a (CanonicalLocalization.physicalAtom K L ρ χ)))‖ ≤
            C*density K L (scale j)) ∧
        ((∀ p ∈ F, p.1.1=p.2.1) →
          ‖CountableAveraging.average volume (envelopeWeight n j i m) (envelopeVolume n j i m)
            (pairSum F (weightedAtoms a (CanonicalLocalization.physicalAtom K L ρ χ)))‖ ≤
              C*sameDensity K L (scale j)) := by
  classical
  obtain ⟨B,hB,havg⟩ := actual_average_decay χ
  refine ⟨B*(crossConstant+sameConstant), mul_pos hB (add_pos crossConstant_pos sameConstant_pos), ?_⟩
  intro K L hK hL n j i hPR hRP hsK ρ hρ hρ1 S hS hc m a ha F hF
  have hL0 : 0 < L := by linarith
  have hs := scale_pos j
  have hs1 : scale j ≤ 1 := by
    unfold scale
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hd : 0 ≤ density K L (scale j) := by unfold density; positivity
  have hd' : 0 ≤ sameDensity K L (scale j) := by unfold sameDensity; positivity
  rcases S.eq_empty_or_nonempty with hSe | hSn
  · have hFe : F=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro p hp
      have hh := hF hp
      simpa [hSe] using hh)
    simp only [hFe, pairSum, Finset.sum_empty, CountableAveraging.average,
      mul_zero, integral_zero, norm_zero]
    have hb0 : 0 ≤ B*(crossConstant+sameConstant) :=
      mul_nonneg hB.le (add_nonneg crossConstant_pos.le sameConstant_pos.le)
    exact ⟨mul_nonneg hb0 hd, fun _ => mul_nonneg hb0 hd'⟩
  obtain ⟨t,ht,ht2,hδ,hangle⟩ := actual_cap_center S hSn K L ρ hK hL0 hρ hρ1 j i hS hc
  have hh := havg K L hK hL0 n j i hPR hRP ρ t (by linarith) hδ m a ha F
  constructor
  · have hb := DensitySums.relation_decay_sum S F hF K L (scale j) t (8*Real.pi)
      hK hL hs hs1 hsK (by linarith) ht2 (by nlinarith [Real.pi_gt_three]) hS hangle
    change (∑ p ∈ F, ((1+DensitySums.distance K L (scale j) t p.1 p.2)^8)⁻¹) ≤
      crossConstant*density K L (scale j) at hb
    calc
      _ ≤ B * ∑ p ∈ F, ((1+DensitySums.distance K L (scale j) t p.1 p.2)^8)⁻¹ := hh
      _ ≤ B*(crossConstant*density K L (scale j)) := mul_le_mul_of_nonneg_left hb hB.le
      _ ≤ B*((crossConstant+sameConstant)*density K L (scale j)) := by
        gcongr; exact le_add_of_nonneg_right sameConstant_pos.le
      _ = _ := by ring
  · intro hsame
    have hF' : F ⊆ (S ×ˢ S).filter (fun p => p.1.1=p.2.1) := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨hF hp, hsame p hp⟩
    have hb := DensitySums.same_relation_decay_sum S F hF' K L (scale j) t (8*Real.pi)
      hK hL hs hs1 hsK (by linarith) ht2 (by nlinarith [Real.pi_gt_three]) hS hangle
    change (∑ p ∈ F, ((1+DensitySums.distance K L (scale j) t p.1 p.2)^8)⁻¹) ≤
      sameConstant*sameDensity K L (scale j) at hb
    calc
      _ ≤ B * ∑ p ∈ F, ((1+DensitySums.distance K L (scale j) t p.1 p.2)^8)⁻¹ := hh
      _ ≤ B*(sameConstant*sameDensity K L (scale j)) := mul_le_mul_of_nonneg_left hb hB.le
      _ ≤ B*((crossConstant+sameConstant)*sameDensity K L (scale j)) := by
        gcongr; exact le_add_of_nonneg_left crossConstant_pos.le
      _ = _ := by ring

end
end CircleDivisor.EnergyV3.LocalDensityActual
