import CircleDivisor.EnergyV3.FirstSpacingAssembly
import CircleDivisor.EnergyV3.LinearTransport

/-! Uniform constants and dyadic thresholds in the final amplitude argument. -/

namespace CircleDivisor.EnergyV3.AmplitudeConstants
noncomputable section
open GuthMaldague MeasureTheory
open scoped ENNReal BigOperators FourierTransform

theorem contributing_mono {C D : ℝ} (hCD : C ≤ D) (ε α : ℝ) (n j : ℕ)
    (i : CapIndex j) (m : Lattice) (f : Space → ℂ) :
    contributing C ε α n j i m f → contributing D ε α n j i m f := by
  intro h
  have hm := localMass_nonneg n j i m f
  have hR := Real.rpow_nonneg (radius_pos n).le ε
  unfold contributing at h ⊢
  apply h.trans
  gcongr

theorem envelopeEnergy_mono {C D : ℝ} (hCD : C ≤ D) (ε α : ℝ) (n j : ℕ)
    (i : CapIndex j) (f : Space → ℂ) :
    envelopeEnergy C ε α n j i f ≤ envelopeEnergy D ε α n j i f := by
  classical
  unfold envelopeEnergy
  apply ENNReal.tsum_le_tsum
  intro m
  by_cases hg : contributing C ε α n j i m f
  · rw [if_pos hg, if_pos (contributing_mono hCD ε α n j i m f hg)]
  · rw [if_neg hg]
    exact bot_le

theorem waveEnvelopeSum_mono {C D : ℝ} (hCD : C ≤ D) (ε α : ℝ) (n : ℕ) (f : Space → ℂ) :
    waveEnvelopeSum C ε α n f ≤ waveEnvelopeSum D ε α n f := by
  unfold waveEnvelopeSum
  exact Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun i hi => envelopeEnergy_mono hCD ε α n j i f))

/-- Enlarging the GM constant also enlarges its amplitude selection. -/
theorem gm_constant_ge_one (hGM : GuthMaldagueInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ f : SchwartzMap Space ℂ, tsupport (𝓕 (f : Space → ℂ)) ⊆
        coneNeighborhood ((radius n)⁻¹) → ∀ α : ℝ, 0 < α →
        ENNReal.ofReal (α ^ (4 : ℕ)) * volume {x : Space | α < ‖f x‖} ≤
          ENNReal.ofReal (C * radius n ^ ε) * waveEnvelopeSum C ε α n f := by
  obtain ⟨C, hC, n₀, hb⟩ := hGM ε hε
  refine ⟨max C 1, le_max_right _ _, n₀, ?_⟩
  intro n hn f hf α hα
  apply (hb n hn f hf α hα).trans
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C 1)
    (Real.rpow_nonneg (radius_pos n).le ε))) (waveEnvelopeSum_mono (le_max_left C 1) ε α n f)

theorem exists_radius_above {P : ℝ} (hP : 1 ≤ P) (n₀ : ℕ) (hlarge : radius n₀ ≤ P) :
    ∃ n : ℕ, n₀ ≤ n ∧ P ≤ radius n ∧ radius n < 4 * P := by
  obtain ⟨n, hPn, hnP⟩ := AmplitudeScale.exists_radius hP
  refine ⟨n, ?_, hPn, hnP⟩
  by_contra hn
  have hlt : radius n < radius n₀ := pow_lt_pow_right₀ (by norm_num) (by omega)
  exact (not_lt_of_ge (hlarge.trans hPn)) hlt

theorem norm_add_rpow_le {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 5) (z w : ℂ) :
    ‖z + w‖ ^ q ≤ 32 * (‖z‖ ^ q + ‖w‖ ^ q) := by
  have htwo : (2 : ℝ) ^ q ≤ 32 := by
    calc
      _ ≤ (2 : ℝ) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hqu
      _ = 32 := by norm_num
  have hbound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
      (a + b) ^ q ≤ 32 * (a ^ q + b ^ q) := by
    calc
      _ ≤ (2 * b) ^ q := Real.rpow_le_rpow (by positivity) (by linarith) hq
      _ = (2 : ℝ) ^ q * b ^ q := Real.mul_rpow (by norm_num) hb
      _ ≤ 32 * b ^ q := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hb _)
      _ ≤ _ := by nlinarith [Real.rpow_nonneg ha q]
  apply (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le z w) hq).trans
  rcases le_total ‖z‖ ‖w‖ with h | h
  · exact hbound _ _ (norm_nonneg _) (norm_nonneg _) h
  · simpa [add_comm] using hbound _ _ (norm_nonneg _) (norm_nonneg _) h

/-- A uniform two-class recombination bound, including integrability. -/
theorem moment_add {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 5)
    (f g : Space → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable (fun x => ‖f x‖ ^ q)) (hgi : Integrable (fun x => ‖g x‖ ^ q)) :
    Integrable (fun x => ‖f x + g x‖ ^ q) ∧
      (∫ x, ‖f x + g x‖ ^ q) ≤ 32 * ((∫ x, ‖f x‖ ^ q) + ∫ x, ‖g x‖ ^ q) := by
  have hmajor := (hfi.add hgi).const_mul 32
  have hmeas : AEStronglyMeasurable (fun x => ‖f x + g x‖ ^ q) volume :=
    ((Real.continuous_rpow_const hq).comp (hf.add hg).norm).aestronglyMeasurable
  have hi : Integrable (fun x => ‖f x + g x‖ ^ q) := hmajor.mono' hmeas (by
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) q)]
    exact norm_add_rpow_le hq hqu (f x) (g x))
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hmajor (fun x => norm_add_rpow_le hq hqu (f x) (g x))
  simpa only [Pi.add_apply, integral_const_mul, integral_add hfi hgi] using hh

end
end CircleDivisor.EnergyV3.AmplitudeConstants
