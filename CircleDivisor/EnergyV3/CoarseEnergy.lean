import CircleDivisor.EnergyV3.CoarseDecomposition
import CircleDivisor.EnergyV3.CrudeEnergy
import CircleDivisor.EnergyV3.RefinedEnergy
import CircleDivisor.EnergyV3.CoarseWindows
import CircleDivisor.EnergyV3.RotationJacobian

/-! Actual same-ray local masses and the signed cross term are connected
to the localized pair averages before applying either energy estimate. -/

namespace CircleDivisor.EnergyV3.CoarseEnergy
noncomputable section
open MeasureTheory GuthMaldague FourierEnergy CoarseDecomposition EnvelopeEnergies
open scoped BigOperators FourierTransform ENNReal
abbrev Space := GuthMaldague.Space
abbrev Point := PairEnergies.Point
abbrev Pair := PairEnergies.Pair

def physicalAtoms (K L : ℝ) (χ : SchwartzMap Space ℂ) (a : Point → ℂ)
    (e : Space ≃L[ℝ] Space) (p : Point) (y : Space) : ℂ := FirstMass.atoms K L χ a p (e y)

theorem pair_average_integrable (n j : ℕ) (i : CapIndex j) (m : Lattice)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4*c ≤ 1)
    (χ : SchwartzMap Space ℂ) (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (e : Space ≃L[ℝ] Space) (P : Finset Pair) :
    Integrable (fun x => (envelopeWeight n j i m x : ℂ) * pairSum P (physicalAtoms K L χ a e) x) :=
  (WeightMass.actual_countable_averaging n j i _
    (LinearTransport.memLp_comp e (localizedPair_memLp K L c hK hL hc χ hχ a ha P))).1 m

theorem same_average (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (K L : ℝ) (χ : SchwartzMap Space ℂ) (a : Point → ℂ) (e : Space ≃L[ℝ] Space)
    (i : CapIndex j) (m : Lattice) :
    envelopePairAverage n j i
      (fun y => localizedPair K L χ a (samePairs (coarsePoints n j I θ i)) (e y)) m =
      (sameMass n j I θ (physicalAtoms K L χ a e) i m : ℂ) := by
  change envelopePairAverage n j i
    (fun x => pairSum ((coarsePoints n j I θ i ×ˢ coarsePoints n j I θ i).filter
      (fun p => p.1.1=p.2.1)) (FirstMass.atoms K L χ a) (e x)) m = _
  rw [FirstMass.envelope_grouped_average n j i m (coarsePoints n j I θ i) Prod.fst]
  congr 1
  unfold sameMass
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [FirstMass.groupedSquare_pairSum]
  rfl

theorem sameEnergy_eq (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4*c ≤ 1)
    (χ : SchwartzMap Space ℂ) (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (e : Space ≃L[ℝ] Space) :
    AmplitudeCountable.sameEnergy n j (sameMass n j I θ (physicalAtoms K L χ a e)) =
      ENNReal.ofReal (RefinedEnergy.familyEnergy n j e K L χ a
        (fun i => samePairs (coarsePoints n j I θ i))) := by
  rw [RefinedEnergy.familyEnergy_ofReal n j e K L c hK hL hc χ hχ a ha]
  unfold AmplitudeCountable.sameEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply tsum_congr
  intro m
  rw [same_average]
  simp

theorem cross_difference (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4*c ≤ 1)
    (χ : SchwartzMap Space ℂ) (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (e : Space ≃L[ℝ] Space) (f : Space → ℂ)
    (hsharp : ∀ b x, capFunction n b f x =
      ∑ p ∈ I.filter (fun p => θ p.1=b), physicalAtoms K L χ a e p x)
    (i : CapIndex j) (m : Lattice) :
    localMass n j i m f - sameMass n j I θ (physicalAtoms K L χ a e) i m =
      (envelopePairAverage n j i (fun y => localizedPair K L χ a
        (crossPairs n (coarsePoints n j I θ i) θ) (e y)) m).re :=
  localMass_sub_sameMass n j I θ _ f hsharp i m
    (fun P => pair_average_integrable n j i m K L c hK hL hc χ hχ a ha e P)

theorem crossEnergy_le (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4*c ≤ 1)
    (χ : SchwartzMap Space ℂ) (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (e : Space ≃L[ℝ] Space) (f : Space → ℂ)
    (hsharp : ∀ b x, capFunction n b f x =
      ∑ p ∈ I.filter (fun p => θ p.1=b), physicalAtoms K L χ a e p x) :
    AmplitudeCountable.crossEnergy n j f (sameMass n j I θ (physicalAtoms K L χ a e)) ≤
      ENNReal.ofReal (RefinedEnergy.familyEnergy n j e K L χ a
        (fun i => crossPairs n (coarsePoints n j I θ i) θ)) := by
  rw [RefinedEnergy.familyEnergy_ofReal n j e K L c hK hL hc χ hχ a ha]
  unfold AmplitudeCountable.crossEnergy
  apply Finset.sum_le_sum
  intro i hi
  apply ENNReal.tsum_le_tsum
  intro m
  apply ENNReal.ofReal_le_ofReal
  rw [cross_difference n j I θ K L c hK hL hc χ hχ a ha e f hsharp i m]
  apply mul_le_mul_of_nonneg_left _ (WeightMass.envelopeVolume_pos n j i m).le
  have hh (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  exact hh _

def firstMassConstant (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space) : ℝ :=
  36 * overlapBound * LinearTransport.jacobian e * (∫ x, ‖χ x‖ ^ 2)

theorem firstMassConstant_nonneg (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space) :
    0 ≤ firstMassConstant χ e := by
  have ho := overlapBound_nonneg
  have he := (LinearTransport.jacobian_pos e).le
  unfold firstMassConstant
  positivity

theorem first_masses (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (hθ : ∀ p∈I, (cap n (θ p.1)).Nonempty)
    (K L c : ℝ) (hL : 1 ≤ L) (hLK : L ≤ K) (hc : 4*c ≤ 1)
    (hI : ∀ p∈I, K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L)
    (χ : SchwartzMap Space ℂ) (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (e : Space ≃L[ℝ] Space) (f : Space → ℂ)
    (hsharp : ∀ b x, capFunction n b f x =
      ∑ p ∈ I.filter (fun p => θ p.1=b), physicalAtoms K L χ a e p x) :
    CrudeEnergy.mass Finset.univ (envelopeVolume n j) (fun i m => localMass n j i m f) ≤
      ENNReal.ofReal (firstMassConstant χ e * (K*L)^3 * (K*L)) ∧
    CrudeEnergy.mass Finset.univ (envelopeVolume n j) (sameMass n j I θ (physicalAtoms K L χ a e)) ≤
      ENNReal.ofReal (firstMassConstant χ e * (K*L)^3 * (K*L)) := by
  have hK : 1 ≤ K := hL.trans hLK
  have hdisj : ((Finset.univ : Finset (CapIndex j)) : Set (CapIndex j)).PairwiseDisjoint (coarsePoints n j I θ) := by
    simpa using coarsePoints_pairwiseDisjoint n j I θ hθ
  have hm := FirstMass.localMass_first_mass n j (coarsePoints n j I θ) I hdisj
    (coarsePoints_subset n j I θ) (fun p => θ p.1) e K L c hK hL (by linarith) hI χ hχ a
    (fun p hp => ha p) f (fun i x => partialSquare_eq_grouped n j I θ _ f hsharp i x)
  have hd := FirstMass.envelope_grouped_first_mass n j (coarsePoints n j I θ) I hdisj
    (coarsePoints_subset n j I θ) Prod.fst e K L c hK hL (by linarith) hI χ hχ a
    (fun p hp => ha p)
  have hterm (i : CapIndex j) (m : Lattice) :
      envelopeVolume n j i m * sameMass n j I θ (physicalAtoms K L χ a e) i m =
        ∫ x, FirstMass.groupedSquare (coarsePoints n j I θ i) Prod.fst (FirstMass.atoms K L χ a) (e x) *
          envelopeWeight n j i m x := by
    unfold sameMass
    rw [mul_div_cancel₀ _ (WeightMass.envelopeVolume_pos n j i m).ne']
    simp_rw [FirstMass.groupedSquare_pairSum]
    rfl
  have hd' : (∀ i : CapIndex j, Summable (fun m : Lattice =>
        envelopeVolume n j i m * sameMass n j I θ (physicalAtoms K L χ a e) i m)) ∧
      (∑ i : CapIndex j, ∑' m : Lattice,
        envelopeVolume n j i m * sameMass n j I θ (physicalAtoms K L χ a e) i m) ≤
          firstMassConstant χ e * (K*L)^3 * (K*L) := by
    simp_rw [hterm]
    exact hd
  constructor
  · rw [CrudeEnergy.mass_ofReal _ _ _ (fun i _ m => mul_nonneg
      (WeightMass.envelopeVolume_pos n j i m).le (localMass_nonneg n j i m f)) (fun i _ => hm.1 i)]
    exact ENNReal.ofReal_le_ofReal hm.2
  · rw [CrudeEnergy.mass_ofReal _ _ _ (fun i _ m => mul_nonneg
      (WeightMass.envelopeVolume_pos n j i m).le (sameMass_nonneg n j I θ _ i m)) (fun i _ => hd'.1 i)]
    exact ENNReal.ofReal_le_ofReal hd'.2

def sameRefinedConstant (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space) : ℝ :=
  48 * CoarseWindows.widthConstant * overlapBound * LinearTransport.jacobian e * (∫ x, ‖χ x‖ ^ 4)

def crossRefinedConstant (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space) (γ C : ℝ) : ℝ :=
  (576 * (1 + 2 * C * (16 * CoarseWindows.widthConstant) ^ γ)) * CoarseWindows.widthConstant ^ 2 *
    overlapBound * LinearTransport.jacobian e * (∫ x, ‖χ x‖ ^ 4)

theorem refined_constants_nonneg (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space)
    (γ C : ℝ) (hC : 0 ≤ C) :
    0 ≤ sameRefinedConstant χ e ∧ 0 ≤ crossRefinedConstant χ e γ C := by
  have hA := CoarseWindows.widthConstant_one_le
  have ho := overlapBound_nonneg
  have hj := (LinearTransport.jacobian_pos e).le
  constructor <;> dsimp [sameRefinedConstant, crossRefinedConstant] <;> positivity

theorem refined_energies (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (K L ρ c γ C : ℝ) (hL : 1 ≤ L) (hLK : L ≤ K) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1)
    (hR : K*L ≤ radius n) (hs : 1 / Real.sqrt (K*L) ≤ scale j) (hc : 4*c ≤ 1)
    (hγ : 0 ≤ γ) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate γ C)
    (hI : ∀ p∈I, K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L)
    (hcap : ∀ p∈I, CoarseWindows.frequency K L ρ p ∈ cap n (θ p.1))
    (χ : SchwartzMap Space ℂ) (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (e : Space ≃L[ℝ] Space) (f : Space → ℂ)
    (hsharp : ∀ b x, capFunction n b f x =
      ∑ p ∈ I.filter (fun p => θ p.1=b), physicalAtoms K L χ a e p x) :
    AmplitudeCountable.sameEnergy n j (sameMass n j I θ (physicalAtoms K L χ a e)) ≤
      ENNReal.ofReal (sameRefinedConstant χ e * (K*L)^3 * (scale j * (K*L)^2 + K*L^3)) ∧
    AmplitudeCountable.crossEnergy n j f (sameMass n j I θ (physicalAtoms K L χ a e)) ≤
      ENNReal.ofReal (crossRefinedConstant χ e γ C * (K*L)^(3+γ) *
        (K^2*L + scale j * K^(5/2:ℝ)*L^(1/2:ℝ))) := by
  have hK : 1 ≤ K := hL.trans hLK
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hθ (p : Point) (hp : p∈I) : (cap n (θ p.1)).Nonempty := ⟨_,hcap p hp⟩
  constructor
  · rw [sameEnergy_eq n j I θ K L c hK hL0 hc χ hχ a ha e]
    apply ENNReal.ofReal_le_ofReal
    exact RefinedEnergy.same_familyEnergy n j e K L (scale j) CoarseWindows.widthConstant c
      hL hLK hs CoarseWindows.widthConstant_one_le hc χ hχ a ha _
      (by simpa using samePairs_pairwiseDisjoint n j I θ hθ)
      (CoarseWindows.sameWindow n j I θ K L ρ hK0 hL0 hρ hρu hI hcap)
  · apply (crossEnergy_le n j I θ K L c hK hL0 hc χ hχ a ha e f hsharp).trans
    apply ENNReal.ofReal_le_ofReal
    exact RefinedEnergy.cross_familyEnergy n j e K L (scale j) CoarseWindows.widthConstant c γ C
      hL hLK hs CoarseWindows.widthConstant_one_le hc hγ hC hdiv χ hχ a ha _
      (by simpa using crossPairs_pairwiseDisjoint n j I θ hθ)
      (CoarseWindows.crossWindow n j I θ K L ρ hK0 hL0 hρ hρu hR hI hcap)

def energyConstant (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space) (A γ C : ℝ) : ℝ :=
  1 + 2*A*firstMassConstant χ e + sameRefinedConstant χ e + crossRefinedConstant χ e γ C

theorem energyConstant_bounds (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space)
    (A γ C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    0 < energyConstant χ e A γ C ∧
      max (A*firstMassConstant χ e) (sameRefinedConstant χ e) ≤ energyConstant χ e A γ C ∧
      max (2*A*firstMassConstant χ e) (crossRefinedConstant χ e γ C) ≤ energyConstant χ e A γ C := by
  obtain ⟨hs,hc⟩ := refined_constants_nonneg χ e γ C hC
  have hf := firstMassConstant_nonneg χ e
  have hAf := mul_nonneg hA hf
  unfold energyConstant
  refine ⟨by nlinarith, max_le_iff.mpr ⟨by nlinarith, by nlinarith⟩,
    max_le_iff.mpr ⟨by nlinarith, by nlinarith⟩⟩

theorem energyConstant_one_le (χ : SchwartzMap Space ℂ) (e : Space ≃L[ℝ] Space)
    (A γ C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) : 1 ≤ energyConstant χ e A γ C := by
  obtain ⟨hs,hc⟩ := refined_constants_nonneg χ e γ C hC
  have hf := mul_nonneg hA (firstMassConstant_nonneg χ e)
  unfold energyConstant
  nlinarith

/-- All refined/crude alternatives are now combined for the actual same
mass and signed cross mass. Only the pointwise local density estimates and
the already constructed sharp-projection identity are premises. -/
theorem profile_energies (n j : ℕ) (I : Finset Point) (θ : ℤ → CapIndex n)
    (K L ρ c A γ C : ℝ) (hL : 1 ≤ L) (hLK : L ≤ K) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1)
    (hR : K*L ≤ radius n) (hs : 1 / Real.sqrt (K*L) ≤ scale j) (hc : 4*c ≤ 1)
    (hA : 0 ≤ A) (hγ : 0 ≤ γ) (hC : 1 ≤ C) (hdiv : SpacingCount.NaturalDivisorEstimate γ C)
    (hI : ∀ p∈I, K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L)
    (hcap : ∀ p∈I, CoarseWindows.frequency K L ρ p ∈ cap n (θ p.1))
    (χ : SchwartzMap Space ℂ) (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (a : Point → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (e : Space ≃L[ℝ] Space) (f : Space → ℂ)
    (hsharp : ∀ b x, capFunction n b f x =
      ∑ p ∈ I.filter (fun p => θ p.1=b), physicalAtoms K L χ a e p x)
    (hd : ∀ i m, sameMass n j I θ (physicalAtoms K L χ a e) i m ≤ A * CircleDivisor.ScaleBounds.D K L (scale j))
    (hb : ∀ i m, |localMass n j i m f - sameMass n j I θ (physicalAtoms K L χ a e) i m| ≤
      A * CircleDivisor.ScaleBounds.M K L (scale j)) :
    AmplitudeCountable.sameEnergy n j (sameMass n j I θ (physicalAtoms K L χ a e)) ≤
      ENNReal.ofReal (energyConstant χ e A γ C * (K*L)^(3+γ) * AmplitudeScale.sameProfile K L (scale j)) ∧
    AmplitudeCountable.crossEnergy n j f (sameMass n j I θ (physicalAtoms K L χ a e)) ≤
      ENNReal.ofReal (energyConstant χ e A γ C * (K*L)^(3+γ) * AmplitudeScale.crossProfile K L (scale j)) := by
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hP : 1 ≤ K*L := one_le_mul_of_one_le_of_one_le (hL.trans hLK) hL
  have hθ (p : Point) (hp : p∈I) : (cap n (θ p.1)).Nonempty := ⟨_,hcap p hp⟩
  obtain ⟨hmM,hmD⟩ := first_masses n j I θ hθ K L c hL hLK hc hI χ hχ a ha e f hsharp
  have hF := firstMassConstant_nonneg χ e
  obtain ⟨hcrudeD,hcrudeC⟩ := CrudeEnergy.actual_profile_crude n j K L A (firstMassConstant χ e) f
    hK0 hL0 hA hF (sameMass n j I θ (physicalAtoms K L χ a e))
    (sameMass_nonneg n j I θ _) hd hb hmM hmD
  obtain ⟨hrefD,hrefC⟩ := refined_energies n j I θ K L ρ c γ C hL hLK hρ hρu hR hs hc hγ hC hdiv
    hI hcap χ hχ a ha e f hsharp
  obtain ⟨hE,hED,hEC⟩ := energyConstant_bounds χ e A γ C hA hC0
  obtain ⟨hsame0,hcross0⟩ := refined_constants_nonneg χ e γ C hC0
  have hdp := (CircleDivisor.ScaleBounds.D_pos hK0 hL0 (scale_pos j)).le
  have hmp := (CircleDivisor.ScaleBounds.M_pos hK0 hL0 (scale_pos j)).le
  have hs0 := (scale_pos j).le
  have hp3 : (K*L)^(3:ℕ) ≤ (K*L)^(3+γ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hP (show (3:ℝ) ≤ 3+γ by linarith)
    norm_num at hh ⊢
    exact hh
  have hrefD' : AmplitudeCountable.sameEnergy n j (sameMass n j I θ (physicalAtoms K L χ a e)) ≤
      ENNReal.ofReal (sameRefinedConstant χ e * (K*L)^(3+γ) * (scale j * (K*L)^2 + K*L^3)) := by
    apply hrefD.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
  have hs := CrudeEnergy.combine_profiles (mul_nonneg hA hF) hP hγ
    (show 0 ≤ (K*L) * CircleDivisor.ScaleBounds.D K L (scale j) by positivity)
    (show 0 ≤ scale j * (K*L)^2 + K*L^3 by have := (scale_pos j).le; positivity) hcrudeD hrefD'
  have hc' := CrudeEnergy.combine_profiles (show 0 ≤ 2*A*firstMassConstant χ e by positivity) hP hγ
    (show 0 ≤ (K*L) * CircleDivisor.ScaleBounds.M K L (scale j) by positivity)
    (show 0 ≤ K^2*L + scale j*K^(5/2:ℝ)*L^(1/2:ℝ) by have := (scale_pos j).le; positivity) hcrudeC hrefC
  obtain ⟨hminD,hminC⟩ := AmplitudeScale.profile_nonneg hK0 hL0 (scale_pos j)
  constructor
  · apply hs.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hED (Real.rpow_nonneg (mul_pos hK0 hL0).le _)) hminD
  · apply hc'.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEC (Real.rpow_nonneg (mul_pos hK0 hL0).le _)) hminC

theorem energyConstant_rotatedPhysical (χ : SchwartzMap Space ℂ) (A γ C ρ : ℝ) :
    energyConstant χ (FourierTransport.rotatedPhysical ρ) A γ C =
      energyConstant χ LinearTransport.circularPhysical A γ C := by
  simp only [energyConstant, firstMassConstant, sameRefinedConstant, crossRefinedConstant,
    RotationJacobian.rotatedPhysical_jacobian]

end
end CircleDivisor.EnergyV3.CoarseEnergy
