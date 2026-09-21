import CircleDivisor.EnergyV3.DensityTransfer
import CircleDivisor.EnergyV3.RotationJacobian
import CircleDivisor.EnergyV3.FirstSpacingAssembly
import CircleDivisor.EnergyV3.AmplitudeConstants
import CircleDivisor.ClassicalInputs

/-! The entire envelope argument for a single actual canonical ray class.
The only external premises are GM and the classical divisor estimate. -/
namespace CircleDivisor.EnergyV3.AnalyticAssembly
noncomputable section
open MeasureTheory GuthMaldague CoarseDecomposition CoarseEnergy
open scoped FourierTransform BigOperators
abbrev Space := GuthMaldague.Space
abbrev Point := CoarseDecomposition.Point

theorem uniform_class_moment_explicit_q
    (χ : SchwartzMap Space ℂ) (c : ℝ) (hc : 4*c≤1)
    (hχ : Function.support (𝓕 (χ : Space→ℂ)) ⊆ Metric.ball 0 c)
    (hGM : GuthMaldagueInput) (hdiv : ClassicalInputs.DivisorBound)
    (ε : ℝ) (hε : 0<ε) :
    ∃ B : ℝ, 0<B ∧ ∃ n₀ : ℕ, ∀ q : ℝ, 4<q → q≤9/2 → ∀ n : ℕ, n₀≤n →
      ∀ K L : ℝ, 1≤L → L≤K → K*L≤radius n → radius n<4*(K*L) →
      ∀ ρ : ℝ, 0≤ρ → ρ≤1 → ∀ I : Finset Point, ∀ θ : ℤ→CapIndex n,
      (∀ p∈I, K≤(p.1:ℝ) ∧ (p.1:ℝ)<2*K ∧ L≤(p.2:ℝ) ∧ (p.2:ℝ)<2*L) →
      (∀ p∈I, CoarseWindows.frequency K L ρ p∈cap n (θ p.1)) →
      ∀ a : Point→ℂ, (∀ p, ‖a p‖≤1) → ∀ f : SchwartzMap Space ℂ,
      (∀ b x, capFunction n b f x = ∑ p∈I.filter (fun p => θ p.1=b),
        physicalAtoms K L χ a (FourierTransport.rotatedPhysical ρ) p x) →
      tsupport (𝓕 (f : Space→ℂ)) ⊆ coneNeighborhood ((radius n)⁻¹) →
      Integrable (fun x => ‖f x‖^q) ∧
        (∫ x, ‖f x‖^q) ≤ B*(q/(q-4))*(K*L)^(3+ε)*Arithmetic.fourTerm K L q := by
  obtain ⟨A,hA,hdens⟩ := DensityTransfer.actual_mass_densities χ
  have hγ : 0<ε/8 := by positivity
  obtain ⟨C,hC,n₀,hGM'⟩ := AmplitudeConstants.gm_constant_ge_one hGM (ε/8) hγ
  obtain ⟨Cdiv,hCdiv,hτ⟩ := hdiv (ε/8) hγ
  have hCdiv1 : 1≤Cdiv := by simpa using hτ 1 (by omega)
  have hτ' : SpacingCount.NaturalDivisorEstimate (ε/8) Cdiv := fun k hk => hτ k (by omega)
  let E := energyConstant χ LinearTransport.circularPhysical A (ε/8) Cdiv
  have hE : 0<E := (energyConstant_bounds χ LinearTransport.circularPhysical A (ε/8) Cdiv
    (by linarith) hCdiv.le).1
  have hEρ (ρ : ℝ) : energyConstant χ (FourierTransport.rotatedPhysical ρ) A (ε/8) Cdiv = E := by
    unfold energyConstant firstMassConstant sameRefinedConstant crossRefinedConstant
    simp only [RotationJacobian.rotatedPhysical_jacobian]
    rfl
  let B := FirstSpacingAssembly.finalConstant C A E 5 ε / 5
  have hB : 0<B := div_pos
    (FirstSpacingAssembly.finalConstant_pos hC hA hE (by norm_num) hε) (by norm_num)
  refine ⟨B,hB,n₀,?_⟩
  intro q hq hqu n hn K L hL hLK hPR hRP ρ hρ hρ1 I θ hI hcap a ha f hsharp hsupport
  have hP : 1≤K*L := one_le_mul_of_one_le_of_one_le (hL.trans hLK) hL
  let D := fun j => sameMass n j I θ (physicalAtoms K L χ a (FourierTransport.rotatedPhysical ρ))
  have hd := hdens K L c hL hLK hc hχ n hPR hRP ρ hρ hρ1 I θ hI hcap a ha f hsharp
  have he (j : ℕ) (hj : j∈Finset.Ioo 0 n) :
      AmplitudeCountable.sameEnergy n j (D j) ≤ ENNReal.ofReal
        ((E*(K*L)^(3+ε/8))*AmplitudeScale.sameProfile K L (scale j)) ∧
      AmplitudeCountable.crossEnergy n j f (D j) ≤ ENNReal.ofReal
        ((E*(K*L)^(3+ε/8))*AmplitudeScale.crossProfile K L (scale j)) := by
    have hh := profile_energies n j I θ K L ρ c A (ε/8) Cdiv hL hLK hρ hρ1 hPR
      (AmplitudeScale.scale_range hP hRP hj).1 hc (by linarith) hγ.le hCdiv1 hτ' hI hcap
      χ hχ a ha (FourierTransport.rotatedPhysical ρ) f hsharp
      (fun i m => (hd j hj i m).1) (fun i m => (hd j hj i m).2)
    simpa only [hEρ] using hh
  have hh := FirstSpacingAssembly.moment_bound K L C A E q ε n f hL hLK hRP hC hA hE hε
    f.continuous.aemeasurable hq hqu D
    (fun j _ i m => sameMass_nonneg n j I θ _ i m)
    (fun j hj i m => (hd j hj i m).1) (fun j hj i m => (hd j hj i m).2)
    (fun j hj => (he j hj).1) (fun j hj => (he j hj).2)
    (hGM' n hn f hsupport)
  convert hh using 1
  dsimp [B, FirstSpacingAssembly.finalConstant]
  congr 1
  ring

end
end CircleDivisor.EnergyV3.AnalyticAssembly
