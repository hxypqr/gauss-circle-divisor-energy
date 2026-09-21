import CircleDivisor.FourierEnergy
import CircleDivisor.SchwartzCutoff

/-!
# Actual Fourier localization and integer orthogonality

The Fourier transform below is Mathlib's Bochner Fourier transform on Euclidean
three-space, with the manuscript's `exp (2 π i x · ξ)` convention.  Starting
from an actual band-limited Schwartz cutoff, we prove support enlargement for
its fourth power, dilation, exact integer orthogonality, the counting bound,
and sharp projection identities for whole atoms.  The final existence theorem
uses the cutoff constructed in `SchwartzCutoff`, with no analytic hypothesis
other than the stated arithmetic size conditions.
-/

open MeasureTheory FourierTransform
open scoped ComplexConjugate RealInnerProductSpace Convolution Pointwise SchwartzMap

namespace CircleDivisor.FourierLocalization

noncomputable section

abbrev Space := EuclideanSpace ℝ (Fin 3)

def character (ξ x : Space) : ℂ := (Real.fourierChar ⟪x, ξ⟫ : ℂ)

@[simp] theorem character_norm (ξ x : Space) : ‖character ξ x‖ = 1 := by
  simp [character]

theorem character_add (ξ η x : Space) :
    character (ξ + η) x = character ξ x * character η x := by
  simp [character, inner_add_right, AddChar.map_add_eq_mul]

theorem character_neg (ξ x : Space) : character (-ξ) x = conj (character ξ x) := by
  simp [character]

theorem character_sub (ξ η x : Space) :
    character (ξ - η) x = character ξ x * conj (character η x) := by
  rw [sub_eq_add_neg, character_add, character_neg]

theorem integral_weighted_character (w : Space → ℂ) (ξ : Space) :
    (∫ x, w x * character ξ x) = 𝓕 w (-ξ) := by
  simp [Real.fourier_eq, character, Circle.smul_def, mul_comm]

/-- Modulation translates the actual Fourier transform with the correct sign. -/
theorem fourier_modulation (w : Space → ℂ) (ξ η : Space) :
    𝓕 (fun x => w x * character ξ x) η = 𝓕 w (η - ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def, smul_eq_mul, ← inner_neg_right]
  change character (-η) x * (w x * character ξ x) = character (-(η - ξ)) x * w x
  have heq : -(η - ξ) = -η + ξ := by module
  rw [heq, character_add]
  ring

theorem support_fourier_modulation (w : Space → ℂ) (ξ : Space) (S : Set Space)
    (hS : Function.support (𝓕 w) ⊆ S) :
    Function.support (𝓕 (fun x => w x * character ξ x)) ⊆ {η | η - ξ ∈ S} := by
  intro η hη
  apply hS
  simpa only [Function.mem_support, fourier_modulation] using hη

theorem support_fourier_modulation_ball (w : Space → ℂ) (ξ : Space) (ρ : ℝ)
    (hS : Function.support (𝓕 w) ⊆ Metric.ball 0 ρ) :
    Function.support (𝓕 (fun x => w x * character ξ x)) ⊆ Metric.ball ξ ρ := by
  intro η hη
  have hh := support_fourier_modulation w ξ (Metric.ball 0 ρ) hS hη
  simpa [Metric.mem_ball, dist_eq_norm] using hh

theorem integrable_weighted_character {w : Space → ℂ} (hw : Integrable w) (ξ : Space) :
    Integrable (fun x => w x * character ξ x) := by
  have h := (Real.fourierIntegral_convergent_iff (-ξ)).mpr hw
  simpa [character, Circle.smul_def, mul_comm] using h

theorem norm_integral_weighted_character_le (w : Space → ℂ) (ξ : Space) :
    ‖∫ x, w x * character ξ x‖ ≤ ∫ x, ‖w x‖ := by
  calc
    _ ≤ ∫ x, ‖w x * character ξ x‖ := norm_integral_le_integral_norm _
    _ = _ := by simp

def localizedAtoms {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space) : ι → Space → ℂ :=
  FourierEnergy.cutoffAtoms χ (fun i => character (ξ i))

def fourthWeight (χ : Space → ℂ) (x : Space) : ℂ := (‖χ x‖ ^ 4 : ℝ)

def secondWeight (χ : Space → ℂ) (x : Space) : ℂ := (‖χ x‖ ^ 2 : ℝ)

theorem localized_pairValue {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (p : ι × ι) (x : Space) :
    FourierEnergy.pairValue (localizedAtoms χ ξ) p x =
      secondWeight χ x * character (ξ p.1 - ξ p.2) x := by
  have hz : χ x * conj (χ x) = secondWeight χ x := by
    simpa [secondWeight, Complex.normSq_eq_norm_sq] using Complex.mul_conj (χ x)
  simp only [FourierEnergy.pairValue, localizedAtoms, FourierEnergy.cutoffAtoms,
    map_mul, character_sub]
  rw [← hz]
  ring

theorem integral_localized_pairValue {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (p : ι × ι) :
    (∫ x, FourierEnergy.pairValue (localizedAtoms χ ξ) p x) =
      𝓕 (secondWeight χ) (ξ p.2 - ξ p.1) := by
  simp_rw [localized_pairValue]
  rw [integral_weighted_character, neg_sub]

def differenceFrequency {ι : Type*} (ξ : ι → Space) (p r : ι × ι) : Space :=
  (ξ p.1 - ξ p.2) - (ξ r.1 - ξ r.2)

theorem quartic_characters {ι : Type*} (ξ : ι → Space) (p r : ι × ι) (x : Space) :
    FourierEnergy.quarticKernel (fun i => character (ξ i)) p r x =
      character (differenceFrequency ξ p r) x := by
  simp [FourierEnergy.quarticKernel, FourierEnergy.pairValue,
    differenceFrequency, character_sub]

theorem localized_quarticKernel {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (p r : ι × ι) (x : Space) :
    FourierEnergy.quarticKernel (localizedAtoms χ ξ) p r x =
      fourthWeight χ x * character (differenceFrequency ξ p r) x := by
  rw [localizedAtoms, FourierEnergy.common_cutoff_quarticKernel, quartic_characters]
  rfl

theorem integral_localized_quarticKernel {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (p r : ι × ι) :
    (∫ x, FourierEnergy.quarticKernel (localizedAtoms χ ξ) p r x) =
      𝓕 (fourthWeight χ) (-differenceFrequency ξ p r) := by
  simp_rw [localized_quarticKernel]
  exact integral_weighted_character _ _

theorem integrable_localized_quarticKernel {ι : Type*} (χ : Space → ℂ) (ξ : ι → Space)
    (hw : Integrable (fourthWeight χ)) (p r : ι × ι) :
    Integrable (FourierEnergy.quarticKernel (localizedAtoms χ ξ) p r) := by
  have heq : FourierEnergy.quarticKernel (localizedAtoms χ ξ) p r =
      fun x => fourthWeight χ x * character (differenceFrequency ξ p r) x :=
    funext (localized_quarticKernel χ ξ p r)
  rw [heq]
  exact integrable_weighted_character hw (differenceFrequency ξ p r)

theorem norm_integral_localized_quarticKernel_le {ι : Type*}
    (χ : Space → ℂ) (ξ : ι → Space) (p r : ι × ι) :
    ‖∫ x, FourierEnergy.quarticKernel (localizedAtoms χ ξ) p r x‖ ≤ ∫ x, ‖χ x‖ ^ 4 := by
  simp_rw [localized_quarticKernel]
  simpa [fourthWeight] using norm_integral_weighted_character_le
    (fourthWeight χ) (differenceFrequency ξ p r)

/-- The manuscript's normalized cone frequencies, including its irrational coordinate. -/
def coneFrequency (K L : ℝ) (k l : ℤ) : Space :=
  WithLp.toLp 2 ![(l : ℝ) / L, (l : ℝ) * Real.sqrt k / (L * Real.sqrt K),
    ((k : ℝ) * l) / (K * L)]

@[simp] theorem coneFrequency_zero (K L : ℝ) (k l : ℤ) :
    coneFrequency K L k l 0 = (l : ℝ) / L := rfl

@[simp] theorem coneFrequency_two (K L : ℝ) (k l : ℤ) :
    coneFrequency K L k l 2 = ((k : ℝ) * l) / (K * L) := rfl

theorem scaled_integer_eq_zero (n : ℤ) {S : ℝ} (hS : 0 < S)
    (h : |(n : ℝ) / S| < 1 / S) : n = 0 := by
  rw [abs_div, abs_of_pos hS] at h
  have h' : |(n : ℝ)| < 1 := (div_lt_div_iff_of_pos_right hS).mp h
  rcases abs_lt.mp h' with ⟨hn, hp⟩
  have hn' : (-1 : ℤ) < n := by exact_mod_cast hn
  have hp' : n < (1 : ℤ) := by exact_mod_cast hp
  omega

theorem small_difference_forces_balance {ι : Type*}
    (K L : ℝ) (hK : 1 ≤ K) (hL : 0 < L)
    (ray radial : ι → ℤ) (p r : ι × ι)
    (hsmall : ‖differenceFrequency (fun i => coneFrequency K L (ray i) (radial i)) p r‖ <
      1 / (K * L)) : FourierEnergy.frequencyBalance ray radial p r := by
  let ξ : ι → Space := fun i => coneFrequency K L (ray i) (radial i)
  have hKL : 0 < K * L := mul_pos (by linarith) hL
  have hzero : |differenceFrequency ξ p r 0| < 1 / L := by
    have hh := (PiLp.norm_apply_le (differenceFrequency ξ p r) 0).trans_lt hsmall
    exact (show |differenceFrequency ξ p r 0| < 1 / (K * L) from hh).trans_le
      (one_div_le_one_div_of_le hL (by nlinarith))
  have htwo : |differenceFrequency ξ p r 2| < 1 / (K * L) := by
    exact (PiLp.norm_apply_le (differenceFrequency ξ p r) 2).trans_lt hsmall
  have eqzero : differenceFrequency ξ p r 0 =
      ((radial p.1 - radial p.2 - (radial r.1 - radial r.2) : ℤ) : ℝ) / L := by
    simp [ξ, differenceFrequency, sub_div]
  have eqtwo : differenceFrequency ξ p r 2 =
      ((ray p.1 * radial p.1 - ray p.2 * radial p.2 -
        (ray r.1 * radial r.1 - ray r.2 * radial r.2) : ℤ) : ℝ) / (K * L) := by
    simp [ξ, differenceFrequency, sub_div]
  rw [eqzero] at hzero
  rw [eqtwo] at htwo
  have hz := scaled_integer_eq_zero _ hL hzero
  have ht := scaled_integer_eq_zero _ hKL htwo
  exact ⟨sub_eq_zero.mp hz, sub_eq_zero.mp ht⟩

/-- Nonzero Fourier coefficients of a weight supported in a ball satisfy both
exact integer equations.  The square-root coordinate is deliberately discarded. -/
theorem nonzero_fourier_forces_balance {ι : Type*}
    (K L ρ : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hρ : ρ ≤ 1 / (K * L))
    (ray radial : ι → ℤ) (w : Space → ℂ)
    (hsupport : Function.support (𝓕 w) ⊆ Metric.ball 0 ρ) (p r : ι × ι)
    (hne : 𝓕 w (-differenceFrequency (fun i => coneFrequency K L (ray i) (radial i)) p r) ≠ 0) :
    FourierEnergy.frequencyBalance ray radial p r := by
  apply small_difference_forces_balance K L hK hL ray radial p r
  have hm := hsupport hne
  have hm' : ‖differenceFrequency (fun i => coneFrequency K L (ray i) (radial i)) p r‖ < ρ := by
    simpa [Metric.mem_ball, dist_zero_right] using hm
  exact hm'.trans_le hρ

theorem integral_localized_quarticKernel_eq_zero_of_unbalanced {ι : Type*}
    (K L ρ : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hρ : ρ ≤ 1 / (K * L))
    (ray radial : ι → ℤ) (χ : Space → ℂ)
    (hsupport : Function.support (𝓕 (fourthWeight χ)) ⊆ Metric.ball 0 ρ)
    (p r : ι × ι) (hnot : ¬ FourierEnergy.frequencyBalance ray radial p r) :
    (∫ x, FourierEnergy.quarticKernel
      (localizedAtoms χ (fun i => coneFrequency K L (ray i) (radial i))) p r x) = 0 := by
  rw [integral_localized_quarticKernel]
  by_contra hne
  exact hnot (nonzero_fourier_forces_balance K L ρ hK hL hρ ray radial
    (fourthWeight χ) hsupport p r hne)

/-- This discharges the `hi`, `hzero`, and `hbound` hypotheses of the previous
Fourier-energy module for the actual localized exponential functions. -/
theorem integral_localized_pairSum_norm_sq_le_balanced_card {ι : Type*}
    (K L ρ : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hρ : ρ ≤ 1 / (K * L))
    (ray radial : ι → ℤ) (χ : Space → ℂ)
    (hw : Integrable (fourthWeight χ))
    (hsupport : Function.support (𝓕 (fourthWeight χ)) ⊆ Metric.ball 0 ρ)
    (P : Finset (ι × ι)) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    let f := localizedAtoms χ (fun i => coneFrequency K L (ray i) (radial i))
    Integrable (fun x => ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) ∧
      (∫ x, ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) ≤
        (∫ x, ‖χ x‖ ^ 4) * (FourierEnergy.balancedQuadruples P ray radial).card := by
  dsimp only
  apply FourierEnergy.integral_weighted_pairSum_norm_sq_le_balanced_card
    volume P a ha _ ray radial (∫ x, ‖χ x‖ ^ 4) (integral_nonneg (fun _ => by positivity))
  · intro p hp r hr
    exact integrable_localized_quarticKernel χ _ hw p r
  · intro p hp r hr hnot
    exact integral_localized_quarticKernel_eq_zero_of_unbalanced
      K L ρ hK hL hρ ray radial χ hsupport p r hnot
  · intro p hp r hr hbal
    exact norm_integral_localized_quarticKernel_le χ _ p r

/-! ## Schwartz multiplication and the fourth-power Fourier support -/

def schwartzMul (f g : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g

@[simp] theorem schwartzMul_apply (f g : 𝓢(Space, ℂ)) (x : Space) :
    schwartzMul f g x = f x * g x := rfl

def schwartzConj (f : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f

@[simp] theorem schwartzConj_apply (f : 𝓢(Space, ℂ)) (x : Space) :
    schwartzConj f x = conj (f x) := rfl

theorem fourier_conj (f : Space → ℂ) (ξ : Space) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ)) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp [Circle.smul_def, map_mul]

theorem fourierInv_schwartzMul (f g : 𝓢(Space, ℂ)) :
    𝓕⁻ (schwartzMul f g) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ f) (𝓕⁻ g) := by
  simp [SchwartzMap.convolution, schwartzMul]

theorem support_fourierInv_ball {f : Space → ℂ} {ρ : ℝ}
    (hf : Function.support (𝓕 f) ⊆ Metric.ball 0 ρ) :
    Function.support (𝓕⁻ f) ⊆ Metric.ball 0 ρ := by
  intro ξ hξ
  have hneg : -ξ ∈ Function.support (𝓕 f) := by
    simpa [Function.mem_support, Real.fourierInv_eq_fourier_neg] using hξ
  simpa [Metric.mem_ball, dist_zero_right] using hf hneg

theorem support_fourier_schwartzMul (f g : 𝓢(Space, ℂ)) (r s : ℝ)
    (hf : Function.support (𝓕 (f : Space → ℂ)) ⊆ Metric.ball 0 r)
    (hg : Function.support (𝓕 (g : Space → ℂ)) ⊆ Metric.ball 0 s) :
    Function.support (𝓕 (schwartzMul f g : Space → ℂ)) ⊆ Metric.ball 0 (r + s) := by
  intro ξ hξ
  have hid : 𝓕 (schwartzMul f g : Space → ℂ) ξ =
      ((𝓕⁻ f : 𝓢(Space, ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕⁻ g : 𝓢(Space, ℂ))) (-ξ) := by
    calc
      _ = 𝓕⁻ (schwartzMul f g) (-ξ) := by
        rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg]
      _ = _ := by rw [fourierInv_schwartzMul, SchwartzMap.convolution_apply]
  have hconv : -ξ ∈ Function.support
      ((𝓕⁻ f : 𝓢(Space, ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕⁻ g : 𝓢(Space, ℂ))) := by
    simpa only [Function.mem_support, ← hid] using hξ
  have hsum := MeasureTheory.support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hconv
  rcases hsum with ⟨a, ha, b, hb, hab⟩
  change a + b = -ξ at hab
  have ha' : ‖a‖ < r := by
    have hh := support_fourierInv_ball hf
    simpa [Metric.mem_ball, dist_zero_right] using hh (by
      simpa only [Function.mem_support, SchwartzMap.fourierInv_coe] using ha)
  have hb' : ‖b‖ < s := by
    have hh := support_fourierInv_ball hg
    simpa [Metric.mem_ball, dist_zero_right] using hh (by
      simpa only [Function.mem_support, SchwartzMap.fourierInv_coe] using hb)
  have : ‖a + b‖ < r + s := (norm_add_le a b).trans_lt (add_lt_add ha' hb')
  rw [hab, norm_neg] at this
  simpa [Metric.mem_ball, dist_zero_right] using this

theorem support_fourier_schwartzConj (f : 𝓢(Space, ℂ)) (r : ℝ)
    (hf : Function.support (𝓕 (f : Space → ℂ)) ⊆ Metric.ball 0 r) :
    Function.support (𝓕 (schwartzConj f : Space → ℂ)) ⊆ Metric.ball 0 r := by
  intro ξ hξ
  have heq : (schwartzConj f : Space → ℂ) = fun x => conj (f x) := rfl
  have hneg : -ξ ∈ Function.support (𝓕 (f : Space → ℂ)) := by
    simp only [Function.mem_support, heq, fourier_conj, map_ne_zero] at hξ
    exact hξ
  simpa [Metric.mem_ball, dist_zero_right] using hf hneg

def schwartzFourth (χ : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  schwartzMul (schwartzMul χ (schwartzConj χ)) (schwartzMul χ (schwartzConj χ))

theorem schwartzFourth_coe (χ : 𝓢(Space, ℂ)) :
    (schwartzFourth χ : Space → ℂ) = fourthWeight χ := by
  funext x
  simp [schwartzFourth, fourthWeight, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ring

theorem integrable_fourthWeight (χ : 𝓢(Space, ℂ)) : Integrable (fourthWeight χ) := by
  rw [← schwartzFourth_coe]
  exact (schwartzFourth χ).integrable

/-- The precise `4c` support enlargement used in Section 3.3, proved from
Schwartz multiplication, conjugation, Fourier inversion, and convolution support. -/
theorem support_fourier_fourthWeight (χ : 𝓢(Space, ℂ)) (c : ℝ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c) :
    Function.support (𝓕 (fourthWeight χ)) ⊆ Metric.ball 0 (4 * c) := by
  have htwo := support_fourier_schwartzMul χ (schwartzConj χ) c c hχ
    (support_fourier_schwartzConj χ c hχ)
  have hfour := support_fourier_schwartzMul (schwartzMul χ (schwartzConj χ))
    (schwartzMul χ (schwartzConj χ)) (c + c) (c + c) htwo htwo
  rw [show c + c + (c + c) = 4 * c by ring] at hfour
  simpa only [← schwartzFourth_coe, schwartzFourth] using hfour

/-! ## Dilation to the manuscript's common scale `P = KL` -/

def dilate (P : ℝ) (w : Space → ℂ) (x : Space) : ℂ := w (P⁻¹ • x)

theorem fourier_eq_integral_character (w : Space → ℂ) (ξ : Space) :
    𝓕 w ξ = ∫ x, w x * character (-ξ) x := by
  simpa only [neg_neg] using (integral_weighted_character w (-ξ)).symm

theorem character_smul_inv_smul (P : ℝ) (hP : P ≠ 0) (ξ x : Space) :
    character (P • ξ) (P⁻¹ • x) = character ξ x := by
  simp [character, inner_smul_left, inner_smul_right, hP]

/-- Actual change of variables in the Fourier integral, in dimension three. -/
theorem fourier_dilate (P : ℝ) (hP : 0 < P) (w : Space → ℂ) (ξ : Space) :
    𝓕 (dilate P w) ξ = P ^ 3 • 𝓕 w (P • ξ) := by
  rw [fourier_eq_integral_character]
  calc
    _ = ∫ x, w (P⁻¹ • x) * character (-(P • ξ)) (P⁻¹ • x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← smul_neg, character_smul_inv_smul P hP.ne']
      rfl
    _ = P ^ 3 • ∫ x, w x * character (-(P • ξ)) x := by
      simpa using Measure.integral_comp_inv_smul_of_nonneg volume
        (fun x => w x * character (-(P • ξ)) x) hP.le
    _ = _ := by rw [← fourier_eq_integral_character]

theorem support_fourier_dilate (P : ℝ) (hP : 0 < P) (w : Space → ℂ) (c : ℝ)
    (hw : Function.support (𝓕 w) ⊆ Metric.ball 0 c) :
    Function.support (𝓕 (dilate P w)) ⊆ Metric.ball 0 (c / P) := by
  intro ξ hξ
  have hn : 𝓕 w (P • ξ) ≠ 0 := by
    intro heq
    exact hξ (by rw [fourier_dilate P hP, heq, smul_zero])
  have hh : P * ‖ξ‖ < c := by
    simpa [Metric.mem_ball, dist_zero_right, norm_smul, abs_of_pos hP] using hw hn
  rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hP]
  simpa [mul_comm] using hh

theorem fourthWeight_dilate (P : ℝ) (χ : Space → ℂ) :
    fourthWeight (dilate P χ) = dilate P (fourthWeight χ) := rfl

theorem integrable_fourthWeight_dilate (P : ℝ) (hP : 0 < P) (χ : 𝓢(Space, ℂ)) :
    Integrable (fourthWeight (dilate P χ)) :=
  (integrable_fourthWeight χ).comp_smul (inv_ne_zero hP.ne')

theorem support_fourier_fourthWeight_dilate (P : ℝ) (hP : 0 < P)
    (χ : 𝓢(Space, ℂ)) (c : ℝ)
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c) :
    Function.support (𝓕 (fourthWeight (dilate P χ))) ⊆ Metric.ball 0 (4 * c / P) :=
  support_fourier_dilate P hP (fourthWeight χ) (4 * c) (support_fourier_fourthWeight χ c hχ)

theorem integral_fourthWeight_dilate (P : ℝ) (hP : 0 ≤ P) (χ : Space → ℂ) :
    (∫ x, ‖dilate P χ x‖ ^ 4) = P ^ 3 * ∫ x, ‖χ x‖ ^ 4 := by
  simpa [dilate] using Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x => ‖χ x‖ ^ 4) hP

/-- Section 3.3 for the exact manuscript localizer `χ(z/(KL))`.  All
orthogonality, integrability, support enlargement, and `P³` scaling conditions
are now consequences of a single band-limited Schwartz cutoff. -/
theorem integral_scaled_pairSum_norm_sq_le_balanced_card {ι : Type*}
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (ray radial : ι → ℤ) (χ : 𝓢(Space, ℂ))
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (P : Finset (ι × ι)) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    let f := localizedAtoms (dilate (K * L) χ)
      (fun i => coneFrequency K L (ray i) (radial i))
    Integrable (fun x => ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) ∧
      (∫ x, ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) ≤
        (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 4) *
          (FourierEnergy.balancedQuadruples P ray radial).card := by
  have hKL : 0 < K * L := mul_pos (by linarith) hL
  have hh := integral_localized_pairSum_norm_sq_le_balanced_card
    K L (4 * c / (K * L)) hK hL (div_le_div_of_nonneg_right hc hKL.le)
    ray radial (dilate (K * L) χ) (integrable_fourthWeight_dilate (K * L) hKL χ)
    (support_fourier_fourthWeight_dilate (K * L) hKL χ c hχ) P a ha
  simpa only [integral_fourthWeight_dilate (K * L) hKL.le] using hh

theorem integral_scaled_fourth_moment_le_balanced_card {ι : Type*}
    (K L c : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hc : 4 * c ≤ 1)
    (ray radial : ι → ℤ) (χ : 𝓢(Space, ℂ))
    (hχ : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 c)
    (I : Finset ι) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    let f := localizedAtoms (dilate (K * L) χ)
      (fun i => coneFrequency K L (ray i) (radial i))
    Integrable (fun x => ‖∑ i ∈ I, a i * f i x‖ ^ 4) ∧
      (∫ x, ‖∑ i ∈ I, a i * f i x‖ ^ 4) ≤
        (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 4) *
          (FourierEnergy.balancedQuadruples (I ×ˢ I) ray radial).card := by
  simpa only [FourierEnergy.pairSum_all_pairs_norm_sq, FourierEnergy.weightedAtoms] using
    integral_scaled_pairSum_norm_sq_le_balanced_card K L c hK hL hc
      ray radial χ hχ (I ×ˢ I) a ha

/-! ## Exact sharp Fourier projection when whole atoms avoid sector boundaries -/

def sharpProjection (S : Set Space) (f : Space → ℂ) : Space → ℂ :=
  𝓕⁻ (S.indicator (𝓕 f))

theorem fourier_finite_sum {ι : Type*} (I : Finset ι) (f : ι → Space → ℂ)
    (hf : ∀ i ∈ I, Integrable (f i)) (ξ : Space) :
    𝓕 (fun x => ∑ i ∈ I, f i x) ξ = ∑ i ∈ I, 𝓕 (f i) ξ := by
  simp_rw [Real.fourier_eq, Finset.smul_sum]
  exact integral_finsetSum I (fun i hi => (Real.fourierIntegral_convergent_iff ξ).mpr (hf i hi))

theorem sharpProjection_finite_sum {ι : Type*} (I J : Finset ι) (hJI : J ⊆ I)
    (f : ι → Space → ℂ) (S : Set Space)
    (hcont : ∀ i ∈ J, Continuous (f i))
    (hf : ∀ i ∈ I, Integrable (f i))
    (hF : ∀ i ∈ J, Integrable (𝓕 (f i)))
    (hkeep : ∀ i ∈ J, Function.support (𝓕 (f i)) ⊆ S)
    (hremove : ∀ i ∈ I, i ∉ J → ∀ ξ ∈ S, 𝓕 (f i) ξ = 0) :
    sharpProjection S (fun x => ∑ i ∈ I, f i x) = fun x => ∑ i ∈ J, f i x := by
  classical
  have hfJ : ∀ i ∈ J, Integrable (f i) := fun i hi => hf i (hJI hi)
  have hid : S.indicator (𝓕 (fun x => ∑ i ∈ I, f i x)) =
      𝓕 (fun x => ∑ i ∈ J, f i x) := by
    funext ξ
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ, fourier_finite_sum I f hf,
        fourier_finite_sum J f hfJ]
      symm
      apply Finset.sum_subset hJI
      intro i hi hnot
      exact hremove i hi hnot ξ hξ
    · rw [Set.indicator_of_notMem hξ, fourier_finite_sum J f hfJ]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      by_contra hn
      exact hξ (hkeep i hi hn)
  unfold sharpProjection
  rw [hid]
  have hi : Integrable (fun x => ∑ i ∈ J, f i x) := integrable_finsetSum J hfJ
  have hFi : Integrable (𝓕 (fun x => ∑ i ∈ J, f i x)) := by
    have heq : 𝓕 (fun x => ∑ i ∈ J, f i x) = fun ξ => ∑ i ∈ J, 𝓕 (f i) ξ :=
      funext (fourier_finite_sum J f hfJ)
    rw [heq]
    exact integrable_finsetSum J hF
  have hc : Continuous (fun x => ∑ i ∈ J, f i x) := continuous_finsetSum J hcont
  exact hc.fourierInv_fourier_eq hi hFi

theorem continuous_character (ξ : Space) : Continuous (character ξ) := by
  unfold character
  fun_prop

theorem integrable_fourier_modulation (w : Space → ℂ) (hw : Integrable (𝓕 w))
    (ξ : Space) : Integrable (𝓕 (fun x => w x * character ξ x)) := by
  have heq : 𝓕 (fun x => w x * character ξ x) = fun η => 𝓕 w (η + -ξ) := by
    funext η
    simpa only [sub_eq_add_neg] using fourier_modulation w ξ η
  rw [heq]
  exact hw.comp_add_right (-ξ)

theorem fourier_const_mul (a : ℂ) (w : Space → ℂ) (ξ : Space) :
    𝓕 (fun x => a * w x) ξ = a * 𝓕 w ξ := by
  simp only [fourier_eq_integral_character, mul_assoc, integral_const_mul]

/-- This is the exact sharp-projection claim in Lemma 2.1, once geometry has
put the entire Fourier ball of each retained atom inside or outside the sector.
The geometry of the two angular grids is a separate internal obligation. -/
theorem sharpProjection_modulated_sum {ι : Type*}
    (I J : Finset ι) (hJI : J ⊆ I) (a : ι → ℂ) (ξ : ι → Space)
    (w : Space → ℂ) (hwc : Continuous w) (hwi : Integrable w)
    (hwF : Integrable (𝓕 w)) (c : ℝ)
    (hsupport : Function.support (𝓕 w) ⊆ Metric.ball 0 c)
    (S : Set Space)
    (hkeep : ∀ i ∈ J, Metric.ball (ξ i) c ⊆ S)
    (hremove : ∀ i ∈ I, i ∉ J → Disjoint (Metric.ball (ξ i) c) S) :
    sharpProjection S (fun x => ∑ i ∈ I, a i * (w x * character (ξ i) x)) =
      fun x => ∑ i ∈ J, a i * (w x * character (ξ i) x) := by
  apply sharpProjection_finite_sum I J hJI _ S
  · intro i hi
    exact continuous_const.mul (hwc.mul (continuous_character (ξ i)))
  · intro i hi
    exact (integrable_weighted_character hwi (ξ i)).const_mul (a i)
  · intro i hi
    have heq : 𝓕 (fun x => a i * (w x * character (ξ i) x)) =
        fun η => a i * 𝓕 (fun x => w x * character (ξ i) x) η :=
      funext (fourier_const_mul (a i) _)
    rw [heq]
    exact (integrable_fourier_modulation w hwF (ξ i)).const_mul (a i)
  · intro i hi η hη
    apply hkeep i hi
    apply support_fourier_modulation_ball w (ξ i) c hsupport
    intro heq
    exact hη (by rw [fourier_const_mul, heq, mul_zero])
  · intro i hi hnot η hη
    rw [fourier_const_mul]
    suffices heq : 𝓕 (fun x => w x * character (ξ i) x) η = 0 by simp [heq]
    by_contra hn
    have hb := support_fourier_modulation_ball w (ξ i) c hsupport hn
    exact Set.disjoint_left.mp (hremove i hi hnot) hb hη

theorem dilate_lower_bound (χ : Space → ℂ) (R P : ℝ) (hP : 0 < P)
    (hχ : ∀ x, ‖x‖ ≤ R → (1 / 2 : ℝ) ≤ ‖χ x‖)
    (x : Space) (hx : ‖x‖ ≤ P * R) : (1 / 2 : ℝ) ≤ ‖dilate P χ x‖ := by
  apply hχ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hP)]
  calc
    _ = ‖x‖ / P := by ring
    _ ≤ R := (div_le_iff₀ hP).mpr (by simpa [mul_comm] using hx)

/-- A fixed cutoff, independent of `K`, `L`, the coefficients and the pair
family, exists and satisfies the manuscript's normalized counting bound.
No Fourier support or orthogonality assertion remains as an input here. -/
theorem exists_scaled_energy_cutoff {ι : Type*} (R : ℝ) (hR : 0 ≤ R) :
    ∃ χ : 𝓢(Space, ℂ),
      (∀ P : ℝ, 0 < P → ∀ x : Space, ‖x‖ ≤ P * R →
        (1 / 2 : ℝ) ≤ ‖dilate P χ x‖) ∧
      ∀ (K L : ℝ), 1 ≤ K → 0 < L → ∀ (ray radial : ι → ℤ)
        (P : Finset (ι × ι)) (a : ι → ℂ), (∀ i, ‖a i‖ ≤ 1) →
        let f := localizedAtoms (dilate (K * L) χ)
          (fun i => coneFrequency K L (ray i) (radial i))
        Integrable (fun x => ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) ∧
          (∫ x, ‖FourierEnergy.pairSum P (FourierEnergy.weightedAtoms a f) x‖ ^ 2) /
            (K * L) ^ 3 ≤ (∫ x, ‖χ x‖ ^ 4) *
              (FourierEnergy.balancedQuadruples P ray radial).card := by
  obtain ⟨χ, hs, hlower⟩ := SchwartzCutoff.exists_cutoff R (1 / 8) hR (by norm_num)
  have hs' : Function.support (𝓕 (χ : Space → ℂ)) ⊆ Metric.ball 0 (1 / 8) := by
    simpa only [SchwartzMap.fourier_coe] using hs
  refine ⟨χ, ?_, ?_⟩
  · intro P hP x hx
    exact dilate_lower_bound χ R P hP hlower x hx
  · intro K L hK hL ray radial P a ha
    have hKL : 0 < K * L := mul_pos (by linarith) hL
    have hh := integral_scaled_pairSum_norm_sq_le_balanced_card K L (1 / 8)
      hK hL (by norm_num) ray radial χ hs' P a ha
    refine ⟨hh.1, (div_le_iff₀ (pow_pos hKL 3)).mpr ?_⟩
    calc
      _ ≤ (K * L) ^ 3 * (∫ x, ‖χ x‖ ^ 4) *
          (FourierEnergy.balancedQuadruples P ray radial).card := hh.2
      _ = _ := by ring

end

end CircleDivisor.FourierLocalization
