import CircleDivisor.EnergyV3.FirstMass
import CircleDivisor.EnergyV3.AmplitudeScale

/-! Countable crude energies from the local density and the proved first
mass, including the signed cross term. No cancellation is discarded by
replacing the cross term with a positive pair sum. -/

namespace CircleDivisor.EnergyV3.CrudeEnergy
noncomputable section
open scoped BigOperators ENNReal

def mass {ι κ : Type*} (J : Finset ι) (w f : ι → κ → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ J, ∑' m : κ, ENNReal.ofReal (w i m * f i m)

theorem mass_ofReal {ι κ : Type*} (J : Finset ι) (w f : ι → κ → ℝ)
    (hnn : ∀ i ∈ J, ∀ m, 0 ≤ w i m * f i m)
    (hs : ∀ i ∈ J, Summable (fun m => w i m * f i m)) :
    mass J w f = ENNReal.ofReal (∑ i ∈ J, ∑' m, w i m * f i m) := by
  unfold mass
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => tsum_nonneg (hnn i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  exact (ENNReal.ofReal_tsum_of_nonneg (hnn i hi) (hs i hi)).symm

theorem square_le_density {w D d : ℝ} (hw : 0 ≤ w) (hD : 0 ≤ D) (hd : D ≤ d) :
    w * D ^ 2 ≤ d * (w * D) := by
  have hh := mul_le_mul_of_nonneg_right hd hD
  have hm := mul_le_mul_of_nonneg_left hh hw
  nlinarith

theorem signed_square_le_density {w M D b : ℝ} (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hD : 0 ≤ D) (hb : |M-D| ≤ b) :
    w * (M-D) ^ 2 ≤ b * (w * M + w * D) := by
  have hab : |M-D| ≤ M+D := by rw [abs_le]; constructor <;> linarith
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hb
  have hh := mul_le_mul hb hab (abs_nonneg _) hb0
  have hh' : (M-D)^2 ≤ b*(M+D) := by nlinarith [sq_abs (M-D)]
  have hm := mul_le_mul_of_nonneg_left hh' hw
  nlinarith

theorem square_mass_le {ι κ : Type*} (J : Finset ι) (w D : ι → κ → ℝ) (d F : ℝ)
    (hw : ∀ i ∈ J, ∀ m, 0 ≤ w i m) (hD : ∀ i ∈ J, ∀ m, 0 ≤ D i m)
    (hd : ∀ i ∈ J, ∀ m, D i m ≤ d) (hd0 : 0 ≤ d)
    (hmass : mass J w D ≤ ENNReal.ofReal F) :
    mass J w (fun i m => D i m ^ 2) ≤ ENNReal.ofReal (d * F) := by
  have hh : mass J w (fun i m => D i m ^ 2) ≤ ENNReal.ofReal d * mass J w D := by
    unfold mass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro m
    rw [← ENNReal.ofReal_mul hd0]
    exact ENNReal.ofReal_le_ofReal (square_le_density (hw i hi m) (hD i hi m) (hd i hi m))
  apply hh.trans
  rw [ENNReal.ofReal_mul hd0]
  exact mul_le_mul_right hmass _

theorem signed_square_mass_le {ι κ : Type*} (J : Finset ι) (w M D : ι → κ → ℝ) (b F G : ℝ)
    (hw : ∀ i ∈ J, ∀ m, 0 ≤ w i m) (hM : ∀ i ∈ J, ∀ m, 0 ≤ M i m)
    (hD : ∀ i ∈ J, ∀ m, 0 ≤ D i m) (hb : ∀ i ∈ J, ∀ m, |M i m - D i m| ≤ b)
    (hb0 : 0 ≤ b) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hmassM : mass J w M ≤ ENNReal.ofReal F) (hmassD : mass J w D ≤ ENNReal.ofReal G) :
    mass J w (fun i m => (M i m - D i m) ^ 2) ≤ ENNReal.ofReal (b * (F + G)) := by
  have hh : mass J w (fun i m => (M i m-D i m)^2) ≤
      ENNReal.ofReal b * (mass J w M + mass J w D) := by
    unfold mass
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro m
    rw [← ENNReal.ofReal_add (mul_nonneg (hw i hi m) (hM i hi m))
      (mul_nonneg (hw i hi m) (hD i hi m)), ← ENNReal.ofReal_mul hb0]
    exact ENNReal.ofReal_le_ofReal (signed_square_le_density (hw i hi m) (hM i hi m) (hD i hi m) (hb i hi m))
  apply hh.trans
  rw [ENNReal.ofReal_mul hb0, ENNReal.ofReal_add hF hG]
  exact mul_le_mul_right (add_le_add hmassM hmassD) _

/-- Merge a density-times-first-mass bound with a refined arithmetic bound,
including the harmless `P^γ` promotion on the crude side. -/
theorem combine_profiles {x : ℝ≥0∞} {E₁ E₂ P γ U V : ℝ}
    (hE₁ : 0 ≤ E₁) (hP : 1 ≤ P) (hγ : 0 ≤ γ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hcrude : x ≤ ENNReal.ofReal (E₁ * P ^ (3 : ℕ) * U))
    (hrefined : x ≤ ENNReal.ofReal (E₂ * P ^ (3 + γ) * V)) :
    x ≤ ENNReal.ofReal (max E₁ E₂ * P ^ (3 + γ) * min U V) := by
  have hP0 : 0 < P := by linarith
  have hpow : P ^ (3 : ℕ) ≤ P ^ (3 + γ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hP (show (3 : ℝ) ≤ 3+γ by linarith)
    norm_num at hh ⊢
    exact hh
  by_cases hUV : U ≤ V
  · rw [min_eq_left hUV]
    apply hcrude.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_left E₁ E₂) hpow (by positivity) (hE₁.trans (le_max_left _ _))) hU
  · rw [min_eq_right (le_of_not_ge hUV)]
    apply hrefined.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right E₁ E₂) (Real.rpow_nonneg hP0.le _)) hV

/-- Direct instance for the actual quantities in amplitude integration. -/
theorem actual_crude_energies (n j : ℕ) (f : GuthMaldague.Space → ℂ)
    (D : (i : GuthMaldague.CapIndex j) → GuthMaldague.Lattice → ℝ) (d b F G : ℝ)
    (hD : ∀ i m, 0 ≤ D i m) (hd : ∀ i m, D i m ≤ d)
    (hb : ∀ i m, |GuthMaldague.localMass n j i m f - D i m| ≤ b)
    (hd0 : 0 ≤ d) (hb0 : 0 ≤ b) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hmassM : mass Finset.univ (GuthMaldague.envelopeVolume n j)
      (fun i m => GuthMaldague.localMass n j i m f) ≤ ENNReal.ofReal F)
    (hmassD : mass Finset.univ (GuthMaldague.envelopeVolume n j) D ≤ ENNReal.ofReal G) :
    AmplitudeCountable.sameEnergy n j D ≤ ENNReal.ofReal (d * G) ∧
      AmplitudeCountable.crossEnergy n j f D ≤ ENNReal.ofReal (b * (F+G)) := by
  exact ⟨square_mass_le Finset.univ _ D d G
    (fun i _ m => (WeightMass.envelopeVolume_pos n j i m).le)
    (fun i _ m => hD i m) (fun i _ m => hd i m) hd0 hmassD,
    signed_square_mass_le Finset.univ _ (fun i m => GuthMaldague.localMass n j i m f) D b F G
      (fun i _ m => (WeightMass.envelopeVolume_pos n j i m).le)
      (fun i _ m => GuthMaldague.localMass_nonneg n j i m f)
      (fun i _ m => hD i m) (fun i _ m => hb i m) hb0 hF hG hmassM hmassD⟩

theorem actual_profile_crude (n j : ℕ) (K L A F : ℝ) (f : GuthMaldague.Space → ℂ)
    (hK : 0 < K) (hL : 0 < L) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (D : (i : GuthMaldague.CapIndex j) → GuthMaldague.Lattice → ℝ)
    (hD : ∀ i m, 0 ≤ D i m)
    (hd : ∀ i m, D i m ≤ A * CircleDivisor.ScaleBounds.D K L (GuthMaldague.scale j))
    (hb : ∀ i m, |GuthMaldague.localMass n j i m f - D i m| ≤
      A * CircleDivisor.ScaleBounds.M K L (GuthMaldague.scale j))
    (hmassM : mass Finset.univ (GuthMaldague.envelopeVolume n j)
      (fun i m => GuthMaldague.localMass n j i m f) ≤ ENNReal.ofReal (F * (K*L)^3 * (K*L)))
    (hmassD : mass Finset.univ (GuthMaldague.envelopeVolume n j) D ≤ ENNReal.ofReal (F * (K*L)^3 * (K*L))) :
    AmplitudeCountable.sameEnergy n j D ≤ ENNReal.ofReal
      ((A*F) * (K*L)^3 * ((K*L) * CircleDivisor.ScaleBounds.D K L (GuthMaldague.scale j))) ∧
    AmplitudeCountable.crossEnergy n j f D ≤ ENNReal.ofReal
      ((2*A*F) * (K*L)^3 * ((K*L) * CircleDivisor.ScaleBounds.M K L (GuthMaldague.scale j))) := by
  have hdp := (CircleDivisor.ScaleBounds.D_pos hK hL (GuthMaldague.scale_pos j)).le
  have hmp := (CircleDivisor.ScaleBounds.M_pos hK hL (GuthMaldague.scale_pos j)).le
  have hh := actual_crude_energies n j f D
    (A * CircleDivisor.ScaleBounds.D K L (GuthMaldague.scale j))
    (A * CircleDivisor.ScaleBounds.M K L (GuthMaldague.scale j))
    (F * (K*L)^3 * (K*L)) (F * (K*L)^3 * (K*L)) hD hd hb
    (by positivity) (by positivity) (by positivity) (by positivity) hmassM hmassD
  convert hh using 1 <;> congr 2 <;> ring

end
end CircleDivisor.EnergyV3.CrudeEnergy
