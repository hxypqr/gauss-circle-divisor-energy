import CircleDivisor.EnergyV3.AnalyticAssembly
import CircleDivisor.EnergyV3.UniformFirstSpacingTransfer
import CircleDivisor.EnergyV3.TwoClassLocalization

/-! The new first-spacing theorem, with every internal analytic and
arithmetic step proved. Only the explicitly stated external inputs remain. -/
namespace CircleDivisor.EnergyV3
noncomputable section
open MeasureTheory GuthMaldague
open scoped FourierTransform BigOperators

theorem uniformFirstSpacing_of_external_inputs
    (hGM : GuthMaldagueInput) (hdiv : ClassicalInputs.DivisorBound) :
    UniformFirstSpacingStatement := by
  obtain ⟨χ,hχ,hχlower⟩ := SchwartzCutoff.exists_cutoff 3 (1/256) (by norm_num) (by norm_num)
  have hχ' : Function.support (𝓕 (χ : FourierLocalization.Space→ℂ)) ⊆ Metric.ball 0 (1/256) := by
    simpa only [SchwartzMap.fourier_coe] using hχ
  apply UniformFirstSpacingTransfer.uniformFirstSpacing_of_large_localized χ hχlower
  intro ε hε
  obtain ⟨B,hB,n₀,hclass⟩ := AnalyticAssembly.uniform_class_moment_explicit_q χ (1/256) (by norm_num)
    hχ' hGM hdiv ε hε
  let N := max n₀ 5
  let J := LinearTransport.jacobian LinearTransport.circularPhysical
  have hJ : 0<J := LinearTransport.jacobian_pos _
  refine ⟨radius N, (64/J)*B, one_le_pow₀ (by norm_num), by positivity, ?_⟩
  intro q hq hqu K L hL hLK hlarge a ha
  have hK : 1 ≤ K := hL.trans hLK
  have hK0 : 0<K := by linarith
  have hL0 : 0<L := by linarith
  have hP0 : 0<K*L := mul_pos hK0 hL0
  have hP : 1 ≤ K*L := one_le_mul_of_one_le_of_one_le hK hL
  obtain ⟨n,hn,hPR,hRP⟩ := AmplitudeConstants.exists_radius_above hP N hlarge
  have hn₀ : n₀≤n := (le_max_left n₀ 5).trans hn
  have hn5 : 5≤n := (le_max_right n₀ 5).trans hn
  obtain ⟨b,θ,hball,hproj⟩ := CanonicalLocalization.exists_actual_canonical_projections
    K L (1/256) hK0 hL0 n hn5 hRP (by norm_num) le_rfl χ hχ'
  let ρ := fun d : Bool => AngularAtoms.gridRotation (AngularAtoms.angularWidth n) d
  have hsmall := AngularAtoms.small_atom_conditions n hn5 (K*L) (1/256) hP0 hRP (by norm_num) le_rfl
  have hρ (d : Bool) : 0 ≤ ρ d ∧ ρ d ≤ 1 := by
    have hδ : 0 ≤ AngularAtoms.angularWidth n := by
      unfold AngularAtoms.angularWidth
      have hs := scale_pos n
      positivity
    have hh := AngularAtoms.gridRotation_bounds (AngularAtoms.angularWidth n) hδ d
    exact ⟨by dsimp [ρ]; linarith, hh.2.trans (by linarith [hsmall.2.2.1])⟩
  have hbnd (d : Bool) :
      (∫ y, ‖CanonicalLocalization.localizedSchwartz K L (ρ d) hP0.ne' χ
        (CanonicalLocalization.classPoints K L b d) (fun p => a p.1 p.2) y‖^q) ≤
          B*(q/(q-4))*(K*L)^(3+ε)*Arithmetic.fourTerm K L q := by
    let I := CanonicalLocalization.classPoints K L b d
    let f := CanonicalLocalization.localizedSchwartz K L (ρ d) hP0.ne' χ I (fun p => a p.1 p.2)
    have hIprod : I ⊆ (dyadicIntegers K).product (dyadicIntegers L) := Finset.filter_subset _ _
    have hI (p : ℤ×ℤ) (hp : p∈I) :
        K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L := by
      obtain ⟨hk,hl⟩ := Finset.mem_product.mp (hIprod hp)
      obtain ⟨hk,hku⟩ := AngularAtoms.dyadic_bounds K p.1 hk
      obtain ⟨hl,hlu⟩ := AngularAtoms.dyadic_bounds L p.2 hl
      exact ⟨hk,hku,hl,hlu⟩
    have hcap (p : ℤ×ℤ) (hp : p∈I) : CoarseWindows.frequency K L (ρ d) p∈cap n (θ p.1) := by
      obtain ⟨hp,hbd⟩ := Finset.mem_filter.mp hp
      obtain ⟨hk,hl⟩ := Finset.mem_product.mp hp
      have hh := hball p.1 hk p.2 hl (Metric.mem_ball_self (div_pos (by norm_num) hP0))
      simpa only [hbd, CoarseWindows.frequency, ρ] using hh
    have hsharp (i : CapIndex n) (x : GuthMaldague.Space) :
        capFunction n i f x = ∑ p∈I.filter (fun p => θ p.1=i),
          CoarseEnergy.physicalAtoms K L χ (fun p => a p.1 p.2)
            (FourierTransport.rotatedPhysical (ρ d)) p x := by
      have hh := congrFun (hproj d i (fun p => a p.1 p.2)) x
      change capFunction n i (fun y => ∑ p∈I,
        a p.1 p.2 * CanonicalLocalization.physicalAtom K L (ρ d) χ p y) x = _ at hh
      simpa only [f,CanonicalLocalization.localizedSchwartz_coe, I, ρ,
        CoarseEnergy.physicalAtoms, FirstMass.atoms, CanonicalLocalization.physicalAtom,
        FourierEnergy.weightedAtoms, FourierLocalization.localizedAtoms,
        FourierEnergy.cutoffAtoms, mul_assoc] using hh
    have hsupport : tsupport (𝓕 (f : FourierLocalization.Space→ℂ)) ⊆ coneNeighborhood ((radius n)⁻¹) := by
      apply CanonicalLocalization.localizedSchwartz_tsupport K L (ρ d) (1/256) hK0 hL0 χ I hIprod
        (fun p => a p.1 p.2) hχ'
      simpa only [scale_sq_eq_radius_inv] using hsmall.2.2.2.2
    exact (hclass q hq hqu n hn₀ K L hL hLK hPR hRP (ρ d) (hρ d).1 (hρ d).2 I θ hI hcap
      (fun p => a p.1 p.2) (fun p => ha p.1 p.2) f hsharp hsupport).2
  have hh := TwoClassLocalization.localized_moment_le_uniform_classes K L q
    (B*(q/(q-4))*(K*L)^(3+ε)*Arithmetic.fourTerm K L q) hP0.ne' (by linarith) (by linarith) χ a b ρ hbnd
  calc
    _ ≤ _ := hh
    _ = _ := by dsimp [J]; ring

theorem firstSpacing_of_external_inputs
    (hGM : GuthMaldagueInput) (hdiv : ClassicalInputs.DivisorBound) :
    FirstSpacingStatement :=
  firstSpacing_of_uniform (uniformFirstSpacing_of_external_inputs hGM hdiv)

end
end CircleDivisor.EnergyV3
