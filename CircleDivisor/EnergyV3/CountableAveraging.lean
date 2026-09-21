import Mathlib

/-! The manuscript's countable averaging lemma for actual weighted Bochner
integrals. No local energy inequality is included as an external assumption. -/

namespace CircleDivisor.EnergyV3.CountableAveraging
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weighted_integrable {g : X → ℂ} {w : X → ℝ} {B : ℝ}
    (hg : MemLp g 2 μ) (hw : Integrable w μ)
    (hw₀ : ∀ x, 0 ≤ w x) (hwB : ∀ x, w x ≤ B) :
    Integrable (fun x => ‖g x‖ ^ 2 * w x) μ ∧
      Integrable (fun x => (w x : ℂ) * g x) μ := by
  have hsq : Integrable (fun x => ‖g x‖ ^ 2 * w x) μ :=
    hg.norm.integrable_sq.mul_bdd hw.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_of_nonneg (hw₀ x)] using hwB x)
  refine ⟨hsq, ?_⟩
  apply (hsq.add hw).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
      hg.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(w x : ℂ) * g x‖ ≤ ‖g x‖ ^ 2 * w x + w x
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw₀ x)]
  have h := mul_nonneg (hw₀ x) (sq_nonneg (‖g x‖ - 1))
  nlinarith [mul_nonneg (hw₀ x) (norm_nonneg (g x))]

theorem weighted_cauchy_schwarz {g : X → ℂ} {w : X → ℝ} {B : ℝ}
    (hg : MemLp g 2 μ) (hw : Integrable w μ)
    (hw₀ : ∀ x, 0 ≤ w x) (hwB : ∀ x, w x ≤ B) :
    ‖∫ x, (w x : ℂ) * g x ∂μ‖ ^ 2 ≤
      (∫ x, w x ∂μ) * ∫ x, ‖g x‖ ^ 2 * w x ∂μ := by
  have hsq := (weighted_integrable hg hw hw₀ hwB).1
  let u : X → ℝ := fun x => ‖g x‖ * Real.sqrt (w x)
  let v : X → ℝ := fun x => Real.sqrt (w x)
  have hu : AEStronglyMeasurable u μ := by
    exact hg.aestronglyMeasurable.norm.mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable)
  have hv : AEStronglyMeasurable v μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hu2 : (fun x => u x ^ 2) = (fun x => ‖g x‖ ^ 2 * w x) := by
    funext x
    simp [u, mul_pow, Real.sq_sqrt (hw₀ x)]
  have hv2 : (fun x => v x ^ 2) = w := by
    funext x
    exact Real.sq_sqrt (hw₀ x)
  have hup : MemLp u 2 μ := (memLp_two_iff_integrable_sq hu).2 (hu2 ▸ hsq)
  have hvp : MemLp v 2 μ := (memLp_two_iff_integrable_sq hv).2 (hv2 ▸ hw)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (p := (2 : ℝ)) (q := (2 : ℝ))
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (show ∀ x, 0 ≤ u x by intro x; dsimp [u]; positivity))
    (Filter.Eventually.of_forall (show ∀ x, 0 ≤ v x by intro x; dsimp [v]; positivity))
    (by simpa using hup) (by simpa using hvp)
  simp only [Real.rpow_two, hu2, hv2] at hh
  have hprod : (fun x => u x * v x) = (fun x => ‖g x‖ * w x) := by
    funext x
    dsimp [u, v]
    rw [mul_assoc, ← pow_two, Real.sq_sqrt (hw₀ x)]
  rw [hprod] at hh
  have hnorm : ‖∫ x, (w x : ℂ) * g x ∂μ‖ ≤ ∫ x, ‖g x‖ * w x ∂μ := by
    convert norm_integral_le_integral_norm (f := fun x => (w x : ℂ) * g x) using 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Real.norm_of_nonneg (hw₀ x), mul_comm]
  have he : 0 ≤ ∫ x, ‖g x‖ ^ 2 * w x ∂μ :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw₀ x))
  have hm : 0 ≤ ∫ x, w x ∂μ := integral_nonneg hw₀
  have hroot : ((∫ x, ‖g x‖ ^ 2 * w x ∂μ) ^ (1 / (2 : ℝ)) *
      (∫ x, w x ∂μ) ^ (1 / (2 : ℝ))) ^ 2 =
        (∫ x, w x ∂μ) * ∫ x, ‖g x‖ ^ 2 * w x ∂μ := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt he, Real.sq_sqrt hm]
    ring
  have hh' := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hnorm.trans hh)
  exact hh'.trans_eq hroot

def average (μ : Measure X) (w : X → ℝ) (volume : ℝ) (g : X → ℂ) : ℂ :=
  (volume : ℂ)⁻¹ * ∫ x, (w x : ℂ) * g x ∂μ

theorem average_energy_le {g : X → ℂ} {w : X → ℝ} {B V c₀ : ℝ}
    (hg : MemLp g 2 μ) (hw : Integrable w μ)
    (hw₀ : ∀ x, 0 ≤ w x) (hwB : ∀ x, w x ≤ B)
    (hV : 0 < V) (hmass : ∫ x, w x ∂μ = c₀ * V) :
    V * ‖average μ w V g‖ ^ 2 ≤ c₀ * ∫ x, ‖g x‖ ^ 2 * w x ∂μ := by
  have hcs := weighted_cauchy_schwarz hg hw hw₀ hwB
  rw [hmass] at hcs
  unfold average
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hV.le]
  calc
    V * (V⁻¹ * ‖∫ x, (w x : ℂ) * g x ∂μ‖) ^ 2 =
        ‖∫ x, (w x : ℂ) * g x ∂μ‖ ^ 2 / V := by field_simp
    _ ≤ c₀ * ∫ x, ‖g x‖ ^ 2 * w x ∂μ :=
      (div_le_iff₀ hV).mpr (by nlinarith [hcs])

/-- Finite overlap controls all the actual weighted averages, before taking
any infinite sum. This formulation has no hidden summability convention. -/
theorem finite_averaging {ι : Type*} (I : Finset ι) (w : ι → X → ℝ) (V : ι → ℝ)
    (g : X → ℂ) (c₀ C : ℝ) (hg : MemLp g 2 μ) (hc₀ : 0 ≤ c₀)
    (hw : ∀ i, Integrable (w i) μ) (hw₀ : ∀ i x, 0 ≤ w i x)
    (hV : ∀ i, 0 < V i) (hmass : ∀ i, ∫ x, w i x ∂μ = c₀ * V i)
    (hoverlap : ∀ J : Finset ι, ∀ x, ∑ i ∈ J, w i x ≤ C) :
    ∑ i ∈ I, V i * ‖average μ (w i) (V i) g‖ ^ 2 ≤
      c₀ * C * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  classical
  have hwB (i : ι) (x : X) : w i x ≤ C := by simpa using hoverlap {i} x
  have hi (i : ι) : Integrable (fun x => ‖g x‖ ^ 2 * w i x) μ :=
    (weighted_integrable hg (hw i) (hw₀ i) (hwB i)).1
  calc
    _ ≤ ∑ i ∈ I, c₀ * ∫ x, ‖g x‖ ^ 2 * w i x ∂μ := by
      exact Finset.sum_le_sum fun i _ => average_energy_le hg (hw i) (hw₀ i) (hwB i)
        (hV i) (hmass i)
    _ = c₀ * ∫ x, ‖g x‖ ^ 2 * (∑ i ∈ I, w i x) ∂μ := by
      rw [← Finset.mul_sum, ← integral_finsetSum I (fun i _ => hi i)]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Finset.mul_sum]
    _ ≤ c₀ * ∫ x, C * ‖g x‖ ^ 2 ∂μ := by
      apply mul_le_mul_of_nonneg_left _ hc₀
      refine integral_mono ?_ (hg.norm.integrable_sq.const_mul C) ?_
      · simpa only [Finset.mul_sum] using integrable_finsetSum I (fun i _ => hi i)
      · intro x
        nlinarith [mul_le_mul_of_nonneg_left (hoverlap I x) (sq_nonneg ‖g x‖)]
    _ = c₀ * C * ∫ x, ‖g x‖ ^ 2 ∂μ := by rw [integral_const_mul]; ring

/-- The countable averaging inequality, with convergence as part of the
conclusion. In fact the finite-overlap proof works for any index type. -/
theorem countable_averaging {ι : Type*} (w : ι → X → ℝ) (V : ι → ℝ)
    (g : X → ℂ) (c₀ C : ℝ) (hg : MemLp g 2 μ) (hc₀ : 0 ≤ c₀)
    (hw : ∀ i, Integrable (w i) μ) (hw₀ : ∀ i x, 0 ≤ w i x)
    (hV : ∀ i, 0 < V i) (hmass : ∀ i, ∫ x, w i x ∂μ = c₀ * V i)
    (hoverlap : ∀ J : Finset ι, ∀ x, ∑ i ∈ J, w i x ≤ C) :
    (∀ i, Integrable (fun x => (w i x : ℂ) * g x) μ) ∧
    Summable (fun i => V i * ‖average μ (w i) (V i) g‖ ^ 2) ∧
    (∑' i, V i * ‖average μ (w i) (V i) g‖ ^ 2) ≤
      c₀ * C * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  classical
  have hnn : 0 ≤ (fun i => V i * ‖average μ (w i) (V i) g‖ ^ 2) :=
    fun i => mul_nonneg (hV i).le (sq_nonneg _)
  have hfinite (I : Finset ι) := finite_averaging I w V g c₀ C hg hc₀ hw hw₀ hV hmass hoverlap
  refine ⟨?_, summable_of_sum_le hnn hfinite, Real.tsum_le_of_sum_le hnn hfinite⟩
  intro i
  exact (weighted_integrable hg (hw i) (hw₀ i)
    (fun x => by simpa using hoverlap {i} x)).2

end
end CircleDivisor.EnergyV3.CountableAveraging
