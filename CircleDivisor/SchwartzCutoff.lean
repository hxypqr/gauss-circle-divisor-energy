import Mathlib

/-! Construction of the common band-limited Schwartz cutoff in Section 2.1. -/

namespace CircleDivisor.SchwartzCutoff
noncomputable section
open MeasureTheory Function
open scoped FourierTransform RealInnerProductSpace ContDiff

abbrev Space := EuclideanSpace ℝ (Fin 3)

theorem fourierChar_sub_one_bound (t : ℝ) :
    ‖(Real.fourierChar t : ℂ) - 1‖ ≤ 2 * Real.pi * |t| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t)
  simpa [Real.fourierChar_apply, mul_comm Complex.I,
    Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using h

/-- A normalized nonnegative compactly supported frequency bump has an inverse
Fourier transform quantitatively close to one near the origin. -/
theorem inverse_close_to_one (u : Space → ℝ) (hu : Integrable u)
    (hnn : ∀ ξ, 0 ≤ u ξ) (hone : ∫ ξ, u ξ = 1)
    (δ : ℝ) (_hδ : 0 ≤ δ) (hsupp : ∀ ξ, δ < ‖ξ‖ → u ξ = 0) (x : Space) :
    ‖𝓕⁻ (fun ξ => (u ξ : ℂ)) x - 1‖ ≤ 2 * Real.pi * δ * ‖x‖ := by
  let phase : Space → ℂ := fun ξ => (Real.fourierChar ⟪ξ, x⟫ : ℂ)
  have hiu : Integrable (fun ξ => (u ξ : ℂ)) := hu.ofReal
  have hit : Integrable (fun ξ => phase ξ * (u ξ : ℂ)) := by
    have h := (Real.fourierIntegral_convergent_iff (-x)).2 hiu
    simpa [phase, inner_neg_right, Circle.smul_def] using h
  have hbound : ∀ ξ, ‖(phase ξ - 1) * (u ξ : ℂ)‖ ≤
      (2 * Real.pi * δ * ‖x‖) * u ξ := by
    intro ξ
    by_cases hh : δ < ‖ξ‖
    · simp [hsupp ξ hh]
    · have hb : |⟪ξ, x⟫| ≤ δ * ‖x‖ :=
        (abs_real_inner_le_norm ξ x).trans (mul_le_mul_of_nonneg_right (le_of_not_gt hh) (norm_nonneg x))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn ξ)]
      have hphase := (fourierChar_sub_one_bound ⟪ξ, x⟫).trans
        (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi))
      exact mul_le_mul_of_nonneg_right (by simpa [phase, mul_assoc] using hphase) (hnn ξ)
  have hnorm := norm_integral_le_of_norm_le
    (hu.const_mul (2 * Real.pi * δ * ‖x‖)) (Filter.Eventually.of_forall hbound)
  have hi : (∫ ξ, (u ξ : ℂ)) = 1 := by
    rw [integral_complex_ofReal, hone]
    norm_num
  have hid : (∫ ξ, (phase ξ - 1) * (u ξ : ℂ)) =
      𝓕⁻ (fun ξ => (u ξ : ℂ)) x - 1 := by
    simp_rw [sub_mul, one_mul]
    rw [integral_sub hit hiu, hi, Real.fourierInv_eq]
    simp only [phase, Circle.smul_def, smul_eq_mul]
  rw [hid, integral_const_mul, hone, mul_one] at hnorm
  exact hnorm

/-- Actual Schwartz localizer with compact Fourier support and a lower bound on
an arbitrary prescribed physical ball. No plateau in physical space is asserted. -/
theorem exists_cutoff (R c : ℝ) (hR : 0 ≤ R) (hc : 0 < c) :
    ∃ χ : SchwartzMap Space ℂ,
      Function.support (⇑(𝓕 χ : SchwartzMap Space ℂ)) ⊆ Metric.ball 0 c ∧
      ∀ x : Space, ‖x‖ ≤ R → (1 / 2 : ℝ) ≤ ‖χ x‖ := by
  let δ := min (c / 2) (1 / (4 * Real.pi * (R + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  let b : ContDiffBump (0 : Space) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let u : Space → ℝ := b.normed volume
  have hu : Integrable u := b.integrable_normed
  have hunn : ∀ ξ, 0 ≤ u ξ := fun ξ => b.nonneg_normed ξ
  have huone : ∫ ξ, u ξ = 1 := b.integral_normed
  have hcomp : HasCompactSupport (fun ξ => (u ξ : ℂ)) := by
    exact b.hasCompactSupport_normed.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have hdiff : ContDiff ℝ ∞ (fun ξ => (u ξ : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  let φ : SchwartzMap Space ℂ := hcomp.toSchwartzMap hdiff
  let χ : SchwartzMap Space ℂ := 𝓕⁻ φ
  have hFourier : 𝓕 χ = φ := FourierTransform.fourier_fourierInv_eq φ
  refine ⟨χ, ?_, ?_⟩
  · rw [hFourier]
    intro ξ hξ
    have hnonzero : u ξ ≠ 0 := by
      intro hh
      exact hξ (by change (u ξ : ℂ) = 0; simp [hh])
    have hball : ξ ∈ Metric.ball (0 : Space) δ := by
      have hh : ξ ∈ Function.support (b.normed volume) := hnonzero
      simpa [b.support_normed_eq, b] using hh
    exact Metric.ball_subset_ball (le_trans (min_le_left _ _) (by linarith : c / 2 ≤ c)) hball
  · intro x hx
    have hs : ∀ ξ, δ < ‖ξ‖ → u ξ = 0 := by
      intro ξ hξ
      have hh : ξ ∉ Function.support (b.normed volume) := by
        rw [b.support_normed_eq]
        simpa [b, Metric.mem_ball, dist_zero_right] using (not_lt.mpr hξ.le)
      exact not_not.mp hh
    have hclose := inverse_close_to_one u hu hunn huone δ hδ.le hs x
    have hχ : (χ : Space → ℂ) = 𝓕⁻ (fun ξ => (u ξ : ℂ)) := by
      exact SchwartzMap.fourierInv_coe φ
    have hprod : 2 * Real.pi * δ * ‖x‖ ≤ 1 / 2 := by
      have hδb := min_le_right (c / 2) (1 / (4 * Real.pi * (R + 1)))
      have hden : 0 < 4 * Real.pi * (R + 1) := by positivity
      have hh : δ * (4 * Real.pi * (R + 1)) ≤ 1 := (le_div_iff₀ hden).mp hδb
      nlinarith [mul_nonneg hδ.le (norm_nonneg x), mul_nonneg hδ.le (sub_nonneg.mpr hx), Real.pi_pos]
    have hnorm := norm_sub_norm_le (1 : ℂ) (χ x)
    rw [norm_one, norm_sub_rev] at hnorm
    rw [← hχ] at hclose
    linarith

end
end CircleDivisor.SchwartzCutoff
