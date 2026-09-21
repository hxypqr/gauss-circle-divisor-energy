import CircleDivisor.EnergyV3.FourierTransport
import CircleDivisor.EnergyV3.CapNesting

namespace CircleDivisor.EnergyV3.CanonicalLocalization
open MeasureTheory FourierTransform Finset
open scoped RealInnerProductSpace SchwartzMap
noncomputable section
abbrev Space := FourierLocalization.Space
abbrev Point := ℤ×ℤ

def dilation (P : ℝ) (hP : P ≠ 0) : Space ≃L[ℝ] Space :=
  (LinearEquiv.smulOfNeZero ℝ Space P⁻¹ (inv_ne_zero hP)).toContinuousLinearEquiv

def transformedCutoff (P ρ : ℝ) (hP : P ≠ 0) (χ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((FourierTransport.rotatedPhysical ρ).trans (dilation P hP)) χ

theorem transformedCutoff_apply (P ρ : ℝ) (hP : P ≠ 0) (χ : SchwartzMap Space ℂ) (y : Space) :
    transformedCutoff P ρ hP χ y =
      FourierLocalization.dilate P χ (FourierTransport.rotatedPhysical ρ y) := rfl

theorem transformedCutoff_support (P ρ c : ℝ) (hP : 0 < P) (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c) :
    Function.support (𝓕 (transformedCutoff P ρ hP.ne' χ : Space → ℂ)) ⊆ Metric.ball 0 (c/P) :=
  FourierTransport.support_rotated_cutoff ρ (FourierLocalization.dilate P χ) (c/P)
    (FourierLocalization.support_fourier_dilate P hP χ c hχ)

def classPoints (K L : ℝ) (b : ℤ → Bool) (a : Bool) : Finset Point :=
  ((dyadicIntegers K).product (dyadicIntegers L)).filter (fun p => b p.1=a)

def physicalAtom (K L ρ : ℝ) (χ : SchwartzMap Space ℂ) (p : Point) (y : Space) : ℂ :=
  FourierLocalization.dilate (K*L) χ (FourierTransport.rotatedPhysical ρ y)*
    FourierLocalization.character (FourierLocalization.coneFrequency K L p.1 p.2)
      (FourierTransport.rotatedPhysical ρ y)

theorem physicalAtom_eq (K L ρ : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap Space ℂ) (p : Point) (y : Space) :
    physicalAtom K L ρ χ p y = transformedCutoff (K*L) ρ hP χ y*
      FourierLocalization.character
        (AngularAtoms.rotate ρ (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L p.1 p.2))) y := by
  rw [transformedCutoff_apply]
  unfold physicalAtom FourierLocalization.character
  rw [FourierTransport.rotatedPhysical_pairing]

/-- Complete whole-atom canonical projection for the actual localized
arithmetic polynomial after the physical transpose and one of two rotations.
No sector-containment or Fourier-localization conclusion is assumed. -/
theorem exists_actual_canonical_projections (K L c : ℝ) (hK : 0 < K) (hL : 0 < L)
    (n : ℕ) (hn : 5 ≤ n) (hR : GuthMaldague.radius n < 4*(K*L))
    (hc : 0 ≤ c) (hcu : c ≤ 1/256) (χ : SchwartzMap Space ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c) :
    ∃ b : ℤ → Bool, ∃ θ : ℤ → GuthMaldague.CapIndex n,
      (∀ k ∈ dyadicIntegers K, ∀ l ∈ dyadicIntegers L,
        Metric.ball (AngularAtoms.rotate (AngularAtoms.gridRotation (AngularAtoms.angularWidth n) (b k))
          (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L k l))) (c/(K*L)) ⊆
            GuthMaldague.cap n (θ k)) ∧
      (∀ a : Bool, ∀ i : GuthMaldague.CapIndex n, ∀ coeff : Point → ℂ,
        let ρ := AngularAtoms.gridRotation (AngularAtoms.angularWidth n) a
        GuthMaldague.capFunction n i
          (fun y => ∑ p ∈ classPoints K L b a, coeff p*physicalAtom K L ρ χ p y) =
          fun y => ∑ p ∈ (classPoints K L b a).filter (fun p => θ p.1=i),
            coeff p*physicalAtom K L ρ χ p y) := by
  classical
  have hP : 0 < K*L := mul_pos hK hL
  rcases AngularAtoms.small_atom_conditions n hn (K*L) c hP hR hc hcu with ⟨he,heu,hδ,hsmall,hcone⟩
  obtain ⟨b,θ,hassign⟩ := AngularAtoms.exists_ray_assignment K L hK hL n (c/(K*L)) he heu hδ hsmall hcone
  refine ⟨b,θ,hassign,fun a i coeff => ?_⟩
  dsimp only
  let ρ := AngularAtoms.gridRotation (AngularAtoms.angularWidth n) a
  let w := transformedCutoff (K*L) ρ hP.ne' χ
  have hball (p : Point) (hp : p ∈ classPoints K L b a) :
      Metric.ball (AngularAtoms.rotate ρ (LinearTransport.circularFrequency
        (FourierLocalization.coneFrequency K L p.1 p.2))) (c/(K*L)) ⊆ GuthMaldague.cap n (θ p.1) := by
    rcases Finset.mem_filter.mp hp with ⟨hp,hb⟩
    rcases Finset.mem_product.mp hp with ⟨hk,hl⟩
    simpa only [hb] using hassign p.1 hk p.2 hl
  have hh := AngularAtoms.sharpProjection_assigned_caps (classPoints K L b a) n (fun p => θ p.1)
    (fun p => AngularAtoms.rotate ρ (LinearTransport.circularFrequency
      (FourierLocalization.coneFrequency K L p.1 p.2))) (c/(K*L)) hball w w.continuous w.integrable
      (SchwartzMap.fourierTransformCLM ℂ w).integrable
      (transformedCutoff_support (K*L) ρ c hP χ hχ) coeff i
  simpa only [w, ← physicalAtom_eq K L ρ hP.ne'] using hh

def modulated (w : SchwartzMap Space ℂ) (ξ : Space) : SchwartzMap Space ℂ :=
  FourierTransformInv.fourierInv ((𝓕 w).compSubConstCLM ℂ ξ)

theorem modulated_coe (w : SchwartzMap Space ℂ) (ξ : Space) :
    (modulated w ξ : Space → ℂ) = fun x => w x*FourierLocalization.character ξ x := by
  have hf : ((𝓕 w).compSubConstCLM ℂ ξ : Space → ℂ) =
      𝓕 (fun x => w x*FourierLocalization.character ξ x) := by
    funext η
    simp only [SchwartzMap.compSubConstCLM_apply, SchwartzMap.fourier_coe]
    exact (FourierLocalization.fourier_modulation w ξ η).symm
  change ((FourierTransformInv.fourierInv ((𝓕 w).compSubConstCLM ℂ ξ) : SchwartzMap Space ℂ) : Space → ℂ) = _
  rw [SchwartzMap.fourierInv_coe, hf]
  exact (w.continuous.mul (FourierLocalization.continuous_character ξ)).fourierInv_fourier_eq
    (FourierLocalization.integrable_weighted_character w.integrable ξ)
    (FourierLocalization.integrable_fourier_modulation w (𝓕 w).integrable ξ)

def localizedSchwartz (K L ρ : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap Space ℂ)
    (I : Finset Point) (coeff : Point → ℂ) : SchwartzMap Space ℂ :=
  ∑ p ∈ I, coeff p • modulated (transformedCutoff (K*L) ρ hP χ)
    (AngularAtoms.rotate ρ (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L p.1 p.2)))

theorem localizedSchwartz_coe (K L ρ : ℝ) (hP : K*L ≠ 0) (χ : SchwartzMap Space ℂ)
    (I : Finset Point) (coeff : Point → ℂ) :
    (localizedSchwartz K L ρ hP χ I coeff : Space → ℂ) =
      fun y => ∑ p ∈ I, coeff p*physicalAtom K L ρ χ p y := by
  funext y
  simp only [localizedSchwartz, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show modulated (transformedCutoff (K*L) ρ hP χ)
      (AngularAtoms.rotate ρ (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L p.1 p.2))) y =
      transformedCutoff (K*L) ρ hP χ y*FourierLocalization.character
        (AngularAtoms.rotate ρ (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L p.1 p.2))) y
      from congrFun (modulated_coe _ _) y, ← physicalAtom_eq]

theorem tsupport_finite_atoms {ι : Type*} (I : Finset ι) (coeff : ι → ℂ)
    (w : SchwartzMap Space ℂ) (ξ : ι → Space) (e : ℝ)
    (hws : Function.support (𝓕 (w : Space → ℂ)) ⊆ Metric.ball 0 e) :
    tsupport (𝓕 (fun y => ∑ p ∈ I, coeff p*(w y*FourierLocalization.character (ξ p) y))) ⊆
      ⋃ p ∈ I, Metric.closedBall (ξ p) e := by
  classical
  apply (isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall)).closure_subset_iff.mpr
  intro η hη
  change 𝓕 (fun y => ∑ p ∈ I, coeff p*(w y*FourierLocalization.character (ξ p) y)) η ≠ 0 at hη
  rw [FourierLocalization.fourier_finite_sum I _ (fun p _ =>
    (FourierLocalization.integrable_weighted_character w.integrable (ξ p)).const_mul (coeff p))] at hη
  obtain ⟨p,hp,hpη⟩ := Finset.exists_ne_zero_of_sum_ne_zero hη
  rw [FourierLocalization.fourier_const_mul] at hpη
  have hn : 𝓕 (fun y => w y*FourierLocalization.character (ξ p) y) η ≠ 0 := by
    intro hh
    exact hpη (by rw [hh,mul_zero])
  have hh := FourierLocalization.support_fourier_modulation_ball w (ξ p) e hws hn
  exact Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨hp,Metric.ball_subset_closedBall hh⟩⟩

/-- The actual Schwartz polynomial satisfies the *closed* Fourier support
hypothesis of GM. The strict cone-neighborhood margin survives closure. -/
theorem localizedSchwartz_tsupport (K L ρ c : ℝ) (hK : 0 < K) (hL : 0 < L)
    (χ : SchwartzMap Space ℂ) (I : Finset Point)
    (hI : I ⊆ (dyadicIntegers K).product (dyadicIntegers L)) (coeff : Point → ℂ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (δ : ℝ) (hδ : c/(K*L) < δ) :
    tsupport (𝓕 (localizedSchwartz K L ρ (mul_pos hK hL).ne' χ I coeff : Space → ℂ)) ⊆
      GuthMaldague.coneNeighborhood δ := by
  let ξ (p : Point) := AngularAtoms.rotate ρ
    (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L p.1 p.2))
  rw [localizedSchwartz_coe]
  simp_rw [physicalAtom_eq K L ρ (mul_pos hK hL).ne']
  intro η hη
  have hh := tsupport_finite_atoms I coeff (transformedCutoff (K*L) ρ (mul_pos hK hL).ne' χ)
    ξ (c/(K*L)) (transformedCutoff_support (K*L) ρ c (mul_pos hK hL) χ hχ) hη
  obtain ⟨p,hnear⟩ := Set.mem_iUnion.mp hh
  obtain ⟨hp,hnear⟩ := Set.mem_iUnion.mp hnear
  have hk := AngularAtoms.dyadic_bounds K p.1 (Finset.mem_product.mp (hI hp)).1
  have hl := AngularAtoms.dyadic_bounds L p.2 (Finset.mem_product.mp (hI hp)).2
  have ht := NeighborCount.sqrt_parameter_bounds hK hk.1 hk.2
  refine ⟨ξ p,?_,(Metric.mem_closedBall.mp hnear).trans_lt hδ⟩
  dsimp [ξ]
  rw [AngularAtoms.circularFrequency_generator K L hK hL p.1 p.2 hk.1]
  exact AngularAtoms.rotate_mem_cone ρ (AngularAtoms.generator_mem_cone _ _
    ((le_div_iff₀ hL).mpr (by linarith)) ((div_lt_iff₀ hL).mpr hl.2)
    ht.1 (by nlinarith [ht.2.2]))

theorem classPoints_partition (K L : ℝ) (b : ℤ → Bool) (f : Point → ℂ) :
    (∑ p ∈ classPoints K L b false, f p)+(∑ p ∈ classPoints K L b true, f p) =
      ∑ p ∈ (dyadicIntegers K).product (dyadicIntegers L), f p := by
  classical
  let I := (dyadicIntegers K).product (dyadicIntegers L)
  have hn : (fun p : Point => ¬b p.1=false) = (fun p => b p.1=true) := by
    funext p
    cases b p.1 <;> simp
  simpa only [classPoints, hn] using (Finset.sum_filter_add_sum_filter_not I (fun p : Point => b p.1=false) f)

end
end CircleDivisor.EnergyV3.CanonicalLocalization
