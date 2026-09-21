import Mathlib

/-!
# Integrating independently truncated distribution bounds

This is the internal layer-cake step of Section 4.  Its hypotheses are explicit
distribution-function inequalities for a measurable function, not assumptions
of the desired moment estimate.  No spacing or wave-envelope theorem is
asserted in this file.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CircleDivisor.AmplitudeIntegration

noncomputable section

/-- The integrable kernel left after multiplying a fourth-moment distribution
bound by the layer-cake weight. -/
def truncatedKernel (q A t : ℝ) : ℝ≥0∞ :=
  (Iic A).indicator (fun t : ℝ => ENNReal.ofReal (t ^ (q - 5))) t

theorem truncatedKernel_measurable (q A : ℝ) : Measurable (truncatedKernel q A) := by
  unfold truncatedKernel
  exact (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (q - 5)))).indicator
    measurableSet_Iic

theorem lintegral_truncatedKernel (q A : ℝ) (hq : 4 < q) (hA : 0 ≤ A) :
    ∫⁻ t in Ioi (0 : ℝ), truncatedKernel q A t =
      ENNReal.ofReal (A ^ (q - 4) / (q - 4)) := by
  have hpow : -1 < q - 5 := by linarith
  have hp : 0 < q - 4 := by linarith
  have hi : IntegrableOn (fun t : ℝ => t ^ (q - 5)) (Ioc 0 A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hA).mp
      (intervalIntegral.intervalIntegrable_rpow' hpow)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) A)] (fun t : ℝ => t ^ (q - 5)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have hinter : Iic A ∩ Ioi (0 : ℝ) = Ioc 0 A := by ext t; simp [and_comm]
  unfold truncatedKernel
  rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    hinter, ← ofReal_integral_eq_lintegral_ofReal hi hnn,
    ← intervalIntegral.integral_of_le hA,
    integral_rpow (Or.inl hpow)]
  have he : q - 5 + 1 = q - 4 := by ring
  simp [he, Real.zero_rpow hp.ne']

/-- Removing the fourth power of the threshold without dividing an extended
real number.  This remains valid even if a superlevel set has infinite measure. -/
theorem layer_weight_identity (q t : ℝ) (ht : 0 < t) (v : ℝ≥0∞) :
    ENNReal.ofReal (t ^ (q - 5)) * (ENNReal.ofReal (t ^ (4 : ℕ)) * v) =
      v * ENNReal.ofReal (t ^ (q - 1)) := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  have hp : t ^ (q - 5) * t ^ (4 : ℕ) = t ^ (q - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hp, mul_comm]

/-- A finite family of amplitude cutoffs, each with its own energy. -/
theorem lintegral_moment_of_truncated_distribution
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (I : Finset ι) (f : α → ℝ) (hf : AEMeasurable f μ)
    (hnn : 0 ≤ᵐ[μ] f) (q : ℝ) (hq : 4 < q)
    (C : ℝ≥0∞) (energy : ι → ℝ≥0∞) (cutoff : ι → ℝ)
    (hcutoff : ∀ i ∈ I, 0 ≤ cutoff i)
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (4 : ℕ)) * μ {a | t < f a} ≤
        C * ∑ i ∈ I, if t ≤ cutoff i then energy i else 0) :
    ∫⁻ a, ENNReal.ofReal (f a ^ q) ∂μ ≤
      ENNReal.ofReal q * C *
        ∑ i ∈ I, energy i * ENNReal.ofReal (cutoff i ^ (q - 4) / (q - 4)) := by
  classical
  have hqpos : 0 < q := by linarith
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hnn hf hqpos]
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      μ {a | t < f a} * ENNReal.ofReal (t ^ (q - 1)) ≤
        C * ∑ i ∈ I, energy i * truncatedKernel q (cutoff i) t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have he := mul_le_mul_right (htail t ht) (ENNReal.ofReal (t ^ (q - 5)))
    rw [layer_weight_identity q t ht] at he
    convert he using 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [truncatedKernel, indicator_apply, mem_Iic]
    split_ifs <;> simp [mul_comm, mul_assoc]
  have hmeas : ∀ i ∈ I, Measurable (fun t => energy i * truncatedKernel q (cutoff i) t) :=
    fun i _ => measurable_const.mul (truncatedKernel_measurable q (cutoff i))
  have heval : (∫⁻ t in Ioi (0 : ℝ), C * ∑ i ∈ I, energy i * truncatedKernel q (cutoff i) t) =
      C * ∑ i ∈ I, energy i * ENNReal.ofReal (cutoff i ^ (q - 4) / (q - 4)) := by
    rw [lintegral_const_mul C (Finset.measurable_fun_sum I hmeas), lintegral_finsetSum I hmeas]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_const_mul (energy i) (truncatedKernel_measurable q (cutoff i)),
      lintegral_truncatedKernel q (cutoff i) hq (hcutoff i hi)]
  calc
    _ ≤ ENNReal.ofReal q *
        ∫⁻ t in Ioi (0 : ℝ), C * ∑ i ∈ I, energy i * truncatedKernel q (cutoff i) t :=
      mul_le_mul_right (lintegral_mono_ae hpoint) _
    _ = _ := by rw [heval]; simp only [mul_assoc]

/-- The real-valued conclusion, including integrability, for finite energies.
In particular, this does not rely on the default value of an undefined
Bochner integral. -/
theorem integral_moment_of_truncated_distribution
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (I : Finset ι) (f : α → ℝ) (hf : AEMeasurable f μ)
    (hnn : ∀ a, 0 ≤ f a) (q : ℝ) (hq : 4 < q)
    (C : ℝ) (hC : 0 ≤ C) (energy cutoff : ι → ℝ)
    (henergy : ∀ i ∈ I, 0 ≤ energy i) (hcutoff : ∀ i ∈ I, 0 ≤ cutoff i)
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (4 : ℕ)) * μ {a | t < f a} ≤
        ENNReal.ofReal C * ∑ i ∈ I,
          if t ≤ cutoff i then ENNReal.ofReal (energy i) else 0) :
    Integrable (fun a => f a ^ q) μ ∧
      (∫ a, f a ^ q ∂μ) ≤
        C * q / (q - 4) * ∑ i ∈ I, energy i * cutoff i ^ (q - 4) := by
  have hp : 0 < q - 4 := by linarith
  have hqpos : 0 < q := by linarith
  have hbound := lintegral_moment_of_truncated_distribution μ I f hf
    (Filter.Eventually.of_forall hnn) q hq (ENNReal.ofReal C)
    (fun i => ENNReal.ofReal (energy i)) cutoff hcutoff htail
  have hsumnn : ∀ i ∈ I, 0 ≤ energy i * (cutoff i ^ (q - 4) / (q - 4)) := by
    intro i hi
    exact mul_nonneg (henergy i hi)
      (div_nonneg (Real.rpow_nonneg (hcutoff i hi) _) hp.le)
  have hsum : (∑ i ∈ I, ENNReal.ofReal (energy i) *
      ENNReal.ofReal (cutoff i ^ (q - 4) / (q - 4))) =
      ENNReal.ofReal (∑ i ∈ I, energy i * (cutoff i ^ (q - 4) / (q - 4))) := by
    rw [ENNReal.ofReal_sum_of_nonneg hsumnn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.ofReal_mul (henergy i hi)]
  rw [hsum, ← ENNReal.ofReal_mul hqpos.le,
    ← ENNReal.ofReal_mul (mul_nonneg hqpos.le hC)] at hbound
  have halg : q * C * (∑ i ∈ I, energy i * (cutoff i ^ (q - 4) / (q - 4))) =
      C * q / (q - 4) * ∑ i ∈ I, energy i * cutoff i ^ (q - 4) := by
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    ring
  rw [halg] at hbound
  have hfm : AEMeasurable (fun a => f a ^ q) μ := hf.pow aemeasurable_const
  have hfnn : 0 ≤ᵐ[μ] (fun a => f a ^ q) :=
    Filter.Eventually.of_forall fun a => Real.rpow_nonneg (hnn a) _
  have hint : Integrable (fun a => f a ^ q) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable hfnn).mp
      (ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top))
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hfnn] at hbound
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp hbound
  exact mul_nonneg (div_nonneg (mul_nonneg hC hqpos.le) hp.le)
    (Finset.sum_nonneg fun i hi => mul_nonneg (henergy i hi)
      (Real.rpow_nonneg (hcutoff i hi) _))

/-- Norm-valued version, covering both real and complex exponential sums. -/
theorem integral_norm_moment_of_truncated_distribution
    {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure α)
    (I : Finset ι) (f : α → E) (hf : AEMeasurable f μ)
    (q : ℝ) (hq : 4 < q) (C : ℝ) (hC : 0 ≤ C)
    (energy cutoff : ι → ℝ)
    (henergy : ∀ i ∈ I, 0 ≤ energy i) (hcutoff : ∀ i ∈ I, 0 ≤ cutoff i)
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (4 : ℕ)) * μ {a | t < ‖f a‖} ≤
        ENNReal.ofReal C * ∑ i ∈ I,
          if t ≤ cutoff i then ENNReal.ofReal (energy i) else 0) :
    Integrable (fun a => ‖f a‖ ^ q) μ ∧
      (∫ a, ‖f a‖ ^ q ∂μ) ≤
        C * q / (q - 4) * ∑ i ∈ I, energy i * cutoff i ^ (q - 4) :=
  integral_moment_of_truncated_distribution μ I (fun a => ‖f a‖) hf.norm
    (fun a => norm_nonneg (f a)) q hq C hC energy cutoff henergy hcutoff htail

/-- The two energies have genuinely independent cutoffs.  No comparison
between `sameCutoff` and `crossCutoff` is assumed. -/
theorem integral_norm_moment_two_cutoffs
    {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure α)
    (I : Finset ι) (f : α → E) (hf : AEMeasurable f μ)
    (q : ℝ) (hq : 4 < q) (C : ℝ) (hC : 0 ≤ C)
    (sameEnergy crossEnergy sameCutoff crossCutoff : ι → ℝ)
    (hsE : ∀ i ∈ I, 0 ≤ sameEnergy i) (hcE : ∀ i ∈ I, 0 ≤ crossEnergy i)
    (hsA : ∀ i ∈ I, 0 ≤ sameCutoff i) (hcA : ∀ i ∈ I, 0 ≤ crossCutoff i)
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (4 : ℕ)) * μ {a | t < ‖f a‖} ≤
        ENNReal.ofReal C * ∑ i ∈ I,
          ((if t ≤ sameCutoff i then ENNReal.ofReal (sameEnergy i) else 0) +
           (if t ≤ crossCutoff i then ENNReal.ofReal (crossEnergy i) else 0))) :
    Integrable (fun a => ‖f a‖ ^ q) μ ∧
      (∫ a, ‖f a‖ ^ q ∂μ) ≤ C * q / (q - 4) * ∑ i ∈ I,
        (sameEnergy i * sameCutoff i ^ (q - 4) +
         crossEnergy i * crossCutoff i ^ (q - 4)) := by
  classical
  let energy : ι × Bool → ℝ := fun p => if p.2 then crossEnergy p.1 else sameEnergy p.1
  let cutoff : ι × Bool → ℝ := fun p => if p.2 then crossCutoff p.1 else sameCutoff p.1
  have he : ∀ p ∈ I ×ˢ Finset.univ, 0 ≤ energy p := by
    intro p hp
    have hip := (Finset.mem_product.mp hp).1
    dsimp [energy]
    split_ifs
    · exact hcE p.1 hip
    · exact hsE p.1 hip
  have ha : ∀ p ∈ I ×ˢ Finset.univ, 0 ≤ cutoff p := by
    intro p hp
    have hip := (Finset.mem_product.mp hp).1
    dsimp [cutoff]
    split_ifs
    · exact hcA p.1 hip
    · exact hsA p.1 hip
  have htail' : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (4 : ℕ)) * μ {a | t < ‖f a‖} ≤
        ENNReal.ofReal C * ∑ p ∈ I ×ˢ Finset.univ,
          if t ≤ cutoff p then ENNReal.ofReal (energy p) else 0 := by
    intro t ht
    simpa [Finset.sum_product, energy, cutoff, add_comm] using htail t ht
  have hresult := integral_norm_moment_of_truncated_distribution μ (I ×ˢ Finset.univ)
    f hf q hq C hC energy cutoff he ha htail'
  simpa [Finset.sum_product, energy, cutoff, add_comm] using hresult

end

end CircleDivisor.AmplitudeIntegration
