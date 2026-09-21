import CircleDivisor.EnergyV3.ReductionAbel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! The endpoint regularity of the *actual* Vaaler weight. This is an internal
proof, rather than an extra bounded-variation assumption on the classical input. -/

namespace CircleDivisor.EnergyV3
noncomputable section
open ClassicalInputs Filter
open scoped Topology ContDiff

theorem sinc_contDiffAt_zero : ContDiffAt ℝ ∞ Real.sinc 0 := by
  rw [Real.sinc_eq_dslope]
  obtain ⟨p, hp⟩ := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0)
  exact (show AnalyticAt ℝ (dslope Real.sin 0) 0 from
    ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩).contDiffAt

private def vaalerNearZero (u : ℝ) : ℝ :=
  (1 - u) * Real.cos (Real.pi * u) / Real.sinc (Real.pi * u) + u

theorem vaaler_eq_nearZero {u : ℝ} (hu : u ≠ 1) :
    vaalerWeight u = vaalerNearZero u := by
  by_cases hu0 : u = 0
  · subst u
    simp [vaalerWeight, vaalerNearZero]
  · simp only [vaalerWeight, if_neg hu0, if_neg hu, vaalerNearZero,
      Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hu0), div_div_eq_mul_div]
    ring

theorem vaalerWeight_reflection (u : ℝ) : vaalerWeight (1 - u) = 1 - vaalerWeight u := by
  by_cases hu0 : u = 0
  · subst u
    norm_num [vaalerWeight]
  by_cases hu1 : u = 1
  · subst u
    norm_num [vaalerWeight]
  have h10 : 1 - u ≠ 0 := by intro h; apply hu1; linarith
  have h11 : 1 - u ≠ 1 := by intro h; apply hu0; linarith
  simp only [vaalerWeight, if_neg hu0, if_neg hu1, if_neg h10, if_neg h11]
  simp only [mul_sub, mul_one, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

theorem vaalerWeight_contDiffAt_zero : ContDiffAt ℝ ∞ vaalerWeight 0 := by
  have hs : ContDiffAt ℝ ∞ (fun u : ℝ => Real.sinc (Real.pi * u)) 0 := by
    have hs0 : ContDiffAt ℝ ∞ Real.sinc (Real.pi * 0) := by
      simpa using sinc_contDiffAt_zero
    exact hs0.comp 0 (contDiffAt_const.mul contDiffAt_id)
  have hf : ContDiffAt ℝ ∞ vaalerNearZero 0 := by
    unfold vaalerNearZero
    apply ContDiffAt.add
    · apply ContDiffAt.div
      · exact (contDiffAt_const.sub contDiffAt_id).mul
          ((contDiffAt_const.mul contDiffAt_id).cos)
      · exact hs
      · simp
    · exact contDiffAt_id
  apply hf.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℝ) ≠ 1)] with u hu
  exact vaaler_eq_nearZero hu

theorem vaalerWeight_contDiffAt_one : ContDiffAt ℝ ∞ vaalerWeight 1 := by
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => 1 - vaalerWeight (1 - u)) 1 := by
    apply contDiffAt_const.sub
    have hs1 : ContDiffAt ℝ ∞ vaalerWeight (1 - (1 : ℝ)) := by
      simpa using vaalerWeight_contDiffAt_zero
    exact hs1.comp 1 (contDiffAt_const.sub contDiffAt_id)
  convert hf using 1
  ext u
  rw [vaalerWeight_reflection]
  ring

theorem vaalerWeight_contDiffOn : ContDiffOn ℝ ∞ vaalerWeight (Set.Icc 0 1) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    exact vaalerWeight_contDiffAt_zero.contDiffWithinAt
  by_cases hu1 : u = 1
  · subst u
    exact vaalerWeight_contDiffAt_one.contDiffWithinAt
  have hsin : Real.sin (Real.pi * u) ≠ 0 := by
    apply ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · exact mul_pos Real.pi_pos (lt_of_le_of_ne hu.1 (Ne.symm hu0))
    · nlinarith [Real.pi_pos, lt_of_le_of_ne hu.2 hu1]
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => Real.pi * u * (1 - u) *
      (Real.cos (Real.pi * u) / Real.sin (Real.pi * u)) + u) u := by
    fun_prop
  apply (hf.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [eventually_ne_nhds hu0, eventually_ne_nhds hu1] with v hv0 hv1
  simp [vaalerWeight, hv0, hv1]

/-- One fixed Lipschitz and magnitude constant works at every Fourier cutoff Y.
The endpoint singularities in the cotangent formula have been removed above. -/
theorem exists_vaalerWeight_bounds : ∃ C : ℝ, 1 ≤ C ∧
    (∀ u ∈ Set.Icc (0 : ℝ) 1, |vaalerWeight u| ≤ C) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |vaalerWeight u - vaalerWeight v| ≤ C * |u - v|) := by
  obtain ⟨K, hK⟩ := vaalerWeight_contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_Icc 0 1) isCompact_Icc
  refine ⟨K + 1, by linarith [K.coe_nonneg], ?_, ?_⟩
  · intro u hu
    have hh := hK.norm_sub_le hu (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    simp only [Real.norm_eq_abs, sub_zero] at hh
    have hw0 : vaalerWeight 0 = 1 := by simp [vaalerWeight]
    rw [hw0] at hh
    have htri := abs_sub (vaalerWeight u) 1
    have huabs : |u| ≤ 1 := by rw [abs_of_nonneg hu.1]; exact hu.2
    have hprod := mul_le_mul_of_nonneg_left huabs K.coe_nonneg
    have htri' := abs_add_le (vaalerWeight u - 1) 1
    rw [sub_add_cancel] at htri'
    norm_num at htri'
    linarith
  · intro u hu v hv
    have hh := hK.norm_sub_le hu hv
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))

theorem vaaler_coefficient_abelCost (C : ℝ) (hC : 1 ≤ C)
    (hW : ∀ u ∈ Set.Icc (0 : ℝ) 1, |vaalerWeight u| ≤ C)
    (hLip : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |vaalerWeight u - vaalerWeight v| ≤ C * |u - v|)
    (Y H n : ℕ) (hH : 1 ≤ H) (hn : 1 ≤ n) (hend : H + n ≤ Y + 1) :
    abelCost (fun i => (vaalerSineCoefficient Y (H + i) : ℂ)) n ≤
      (2 * C / Real.pi) / H := by
  let D : ℝ := Y + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hindex (i : ℕ) (hi : i < n) :
      ((H + i : ℕ) : ℝ) / D ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hD]
      dsimp [D]
      exact_mod_cast (by omega : H + i ≤ Y + 1)
  let w : ℕ → ℂ := fun i => (vaalerWeight ((H + i : ℕ) / D) : ℂ)
  let c : ℕ → ℝ := fun i => 1 / (Real.pi * (H + i : ℕ))
  have hw (i : ℕ) (hi : i < n) : ‖w i‖ ≤ C := by
    simpa only [w, Complex.norm_real, Real.norm_eq_abs] using hW _ (hindex i hi)
  have hc0 (i : ℕ) (hi : i < n) : 0 ≤ c i := by dsimp [c]; positivity
  have hcle (i : ℕ) (hi : i < n) : c (i + 1) ≤ c i := by
    dsimp [c]
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_left (by push_cast; linarith) Real.pi_pos.le
  have hc (i : ℕ) (hi : i < n) : ‖(c i : ℂ)‖ ≤ 1 / (Real.pi * H) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 i hi)]
    dsimp [c]
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    push_cast
    exact le_add_of_nonneg_right (Nat.cast_nonneg i)
  have hccost : abelCost (fun i => (c i : ℂ)) n = 1 / (Real.pi * H) := by
    simpa [c] using abelCost_real_antitone c n hn hc0
      (fun i hi => hcle i (by omega))
  have hvardiff (i : ℕ) (hi : i < n - 1) : ‖w (i + 1) - w i‖ ≤ C / D := by
    have hh := hLip _ (hindex (i + 1) (by omega)) _ (hindex i (by omega))
    have hd : ((H + (i + 1) : ℕ) : ℝ) / D - ((H + i : ℕ) : ℝ) / D = 1 / D := by
      push_cast
      ring
    rw [hd, abs_of_pos (one_div_pos.mpr hD)] at hh
    simpa only [w, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      mul_one_div] using hh
  have hvar : ∑ i ∈ Finset.range (n - 1), ‖w (i + 1) - w i‖ ≤ C := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (n - 1), C / D :=
        Finset.sum_le_sum (fun i hi => hvardiff i (Finset.mem_range.mp hi))
      _ = (n - 1 : ℕ) * (C / D) := by simp
      _ ≤ C := by
        have hlen : ((n - 1 : ℕ) : ℝ) ≤ D := by
          dsimp [D]
          exact_mod_cast (by omega : n - 1 ≤ Y + 1)
        rw [← mul_div_assoc, div_le_iff₀ hD]
        nlinarith
  have hh := abelCost_mul w (fun i => (c i : ℂ)) n hn C
    (1 / (Real.pi * H)) hw hc
  rw [hccost] at hh
  have heq : (fun i => (vaalerSineCoefficient Y (H + i) : ℂ)) =
      fun i => w i * (c i : ℂ) := by
    ext i
    simp [vaalerSineCoefficient, w, c, D, div_eq_mul_inv]
  rw [heq]
  calc
    _ ≤ C * (1 / (Real.pi * H)) + (1 / (Real.pi * H)) * C :=
      hh.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ 1 / (Real.pi * H))))
    _ = (2 * C / Real.pi) / H := by field_simp; ring

theorem fejer_coefficient_abelCost (Y H n : ℕ) (hH : 1 ≤ H) (hn : 1 ≤ n)
    (hend : H + n ≤ Y + 1) :
    abelCost (fun i => (fejerCosineCoefficient Y (H + i) : ℂ)) n ≤
      1 / (Y + 1) := by
  have hD : 0 < (Y : ℝ) + 1 := by positivity
  have hnonneg (i : ℕ) (hi : i < n) : 0 ≤ fejerCosineCoefficient Y (H + i) := by
    unfold fejerCosineCoefficient
    apply div_nonneg _ hD.le
    apply sub_nonneg.mpr
    rw [div_le_one hD]
    exact_mod_cast (by omega : H + i ≤ Y + 1)
  have hmono (i : ℕ) (hi : i < n - 1) :
      fejerCosineCoefficient Y (H + (i + 1)) ≤ fejerCosineCoefficient Y (H + i) := by
    unfold fejerCosineCoefficient
    apply div_le_div_of_nonneg_right _ hD.le
    apply sub_le_sub_left
    apply div_le_div_of_nonneg_right _ hD.le
    exact_mod_cast (by omega : H + i ≤ H + (i + 1))
  rw [abelCost_real_antitone (fun i => fejerCosineCoefficient Y (H + i)) n hn
    hnonneg hmono]
  simp only [Nat.add_zero, fejerCosineCoefficient]
  apply div_le_div_of_nonneg_right _ hD.le
  have : 0 ≤ (H : ℝ) / (Y + 1) := by positivity
  linarith

end
end CircleDivisor.EnergyV3
