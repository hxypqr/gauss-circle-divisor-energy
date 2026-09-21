import Mathlib

/-!
# Finite Fourier energy and exact frequency constraints

This file proves the finite expansion and counting step in Section 3.3 for
actual complex-valued functions and Bochner integrals.  Orthogonality of an
individual quartic integral is an explicit *local hypothesis*.  Deriving that
hypothesis from the Fourier support of the common cutoff is a separate task;
it is not declared to be an external theorem here.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace CircleDivisor.FourierEnergy

noncomputable section

def pairValue {α ι : Type*} (f : ι → α → ℂ) (p : ι × ι) (x : α) : ℂ :=
  f p.1 x * conj (f p.2 x)

def pairSum {α ι : Type*} (P : Finset (ι × ι)) (f : ι → α → ℂ) (x : α) : ℂ :=
  ∑ p ∈ P, pairValue f p x

def quarticKernel {α ι : Type*} (f : ι → α → ℂ) (p r : ι × ι) (x : α) : ℂ :=
  pairValue f p x * conj (pairValue f r x)

theorem quarticKernel_explicit {α ι : Type*} (f : ι → α → ℂ)
    (p r : ι × ι) (x : α) :
    quarticKernel f p r x =
      f p.1 x * conj (f p.2 x) * conj (f r.1 x) * f r.2 x := by
  simp [quarticKernel, pairValue, map_mul, mul_assoc]

theorem pairSum_norm_sq_expansion {α ι : Type*}
    (P : Finset (ι × ι)) (f : ι → α → ℂ) (x : α) :
    ‖pairSum P f x‖ ^ 2 = ∑ p ∈ P, ∑ r ∈ P, (quarticKernel f p r x).re := by
  have hmul := congrArg Complex.re (Complex.mul_conj (pairSum P f x))
  rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hmul
  rw [← hmul]
  simp [pairSum, quarticKernel, map_sum, Finset.mul_sum, mul_comm]

theorem integral_pairSum_norm_sq_expansion
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : Finset (ι × ι)) (f : ι → α → ℂ)
    (hi : ∀ p ∈ P, ∀ r ∈ P, Integrable (quarticKernel f p r) μ) :
    (∫ x, ‖pairSum P f x‖ ^ 2 ∂μ) =
      ∑ p ∈ P, ∑ r ∈ P, (∫ x, quarticKernel f p r x ∂μ).re := by
  simp_rw [pairSum_norm_sq_expansion]
  rw [integral_finsetSum P]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_finsetSum P]
    · apply Finset.sum_congr rfl
      intro r hr
      exact integral_re (hi p hp r hr)
    · exact fun r hr => (hi p hp r hr).re
  · intro p hp
    exact integrable_finsetSum P (fun r hr => (hi p hp r hr).re)

theorem integrable_pairSum_norm_sq
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : Finset (ι × ι)) (f : ι → α → ℂ)
    (hi : ∀ p ∈ P, ∀ r ∈ P, Integrable (quarticKernel f p r) μ) :
    Integrable (fun x => ‖pairSum P f x‖ ^ 2) μ := by
  simp_rw [pairSum_norm_sq_expansion]
  exact integrable_finsetSum P (fun p hp =>
    integrable_finsetSum P (fun r hr => (hi p hp r hr).re))

/-- The counting step works for any exact orthogonality constraint. -/
theorem integral_pairSum_norm_sq_le_card
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : Finset (ι × ι)) (f : ι → α → ℂ)
    (constraint : (ι × ι) → (ι × ι) → Prop)
    [DecidablePred (fun pr : (ι × ι) × (ι × ι) => constraint pr.1 pr.2)]
    (B : ℝ) (_hB : 0 ≤ B)
    (hi : ∀ p ∈ P, ∀ r ∈ P, Integrable (quarticKernel f p r) μ)
    (hzero : ∀ p ∈ P, ∀ r ∈ P, ¬ constraint p r →
      (∫ x, quarticKernel f p r x ∂μ) = 0)
    (hbound : ∀ p ∈ P, ∀ r ∈ P, constraint p r →
      ‖∫ x, quarticKernel f p r x ∂μ‖ ≤ B) :
    (∫ x, ‖pairSum P f x‖ ^ 2 ∂μ) ≤
      B * (((P ×ˢ P).filter (fun pr => constraint pr.1 pr.2)).card : ℝ) := by
  classical
  rw [integral_pairSum_norm_sq_expansion μ P f hi]
  calc
    _ = ∑ pr ∈ P ×ˢ P, (∫ x, quarticKernel f pr.1 pr.2 x ∂μ).re :=
      (Finset.sum_product _ _ _).symm
    _ ≤ ∑ pr ∈ P ×ˢ P, if constraint pr.1 pr.2 then B else 0 := by
      apply Finset.sum_le_sum
      intro pr hpr
      rcases Finset.mem_product.mp hpr with ⟨hp, hr⟩
      by_cases hc : constraint pr.1 pr.2
      · simp only [if_pos hc]
        exact (Complex.re_le_norm _).trans (hbound pr.1 hp pr.2 hr hc)
      · simp [hc, hzero pr.1 hp pr.2 hr hc]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [mul_comm]

/-- The two integer frequency equations recovered from small Fourier support. -/
def frequencyBalance {ι : Type*} (ray radial : ι → ℤ) (p r : ι × ι) : Prop :=
  radial p.1 - radial p.2 = radial r.1 - radial r.2 ∧
    ray p.1 * radial p.1 - ray p.2 * radial p.2 =
      ray r.1 * radial r.1 - ray r.2 * radial r.2

instance frequencyBalance_decidable {ι : Type*} (ray radial : ι → ℤ) (p r : ι × ι) :
    Decidable (frequencyBalance ray radial p r) := by
  unfold frequencyBalance
  infer_instance

theorem frequencyBalance_iff_additive {ι : Type*} (ray radial : ι → ℤ) (p r : ι × ι) :
    frequencyBalance ray radial p r ↔
      radial p.1 + radial r.2 = radial p.2 + radial r.1 ∧
      ray p.1 * radial p.1 + ray r.2 * radial r.2 =
        ray p.2 * radial p.2 + ray r.1 * radial r.1 := by
  unfold frequencyBalance
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

def balancedQuadruples {ι : Type*} (P : Finset (ι × ι)) (ray radial : ι → ℤ) :
    Finset ((ι × ι) × (ι × ι)) :=
  (P ×ˢ P).filter fun pr => frequencyBalance ray radial pr.1 pr.2

/-- Actual finite Fourier energy is at most the number of constrained quadruples,
times the per-quadruple integral bound. -/
theorem integral_pairSum_norm_sq_le_balanced_card
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : Finset (ι × ι)) (f : ι → α → ℂ) (ray radial : ι → ℤ)
    (B : ℝ) (hB : 0 ≤ B)
    (hi : ∀ p ∈ P, ∀ r ∈ P, Integrable (quarticKernel f p r) μ)
    (hzero : ∀ p ∈ P, ∀ r ∈ P, ¬ frequencyBalance ray radial p r →
      (∫ x, quarticKernel f p r x ∂μ) = 0)
    (hbound : ∀ p ∈ P, ∀ r ∈ P, frequencyBalance ray radial p r →
      ‖∫ x, quarticKernel f p r x ∂μ‖ ≤ B) :
    (∫ x, ‖pairSum P f x‖ ^ 2 ∂μ) ≤ B * (balancedQuadruples P ray radial).card :=
  integral_pairSum_norm_sq_le_card μ P f (frequencyBalance ray radial) B hB hi hzero hbound

def sameRayPairs {ι : Type*} (I : Finset ι) (ray : ι → ℤ) : Finset (ι × ι) :=
  (I ×ˢ I).filter fun p => ray p.1 = ray p.2

def crossRayPairs {ι : Type*} (I : Finset ι) (ray : ι → ℤ) : Finset (ι × ι) :=
  (I ×ˢ I).filter fun p => ray p.1 ≠ ray p.2

theorem cross_pair_ray_ne {ι : Type*} (I : Finset ι) (ray : ι → ℤ)
    (p : ι × ι) (hp : p ∈ crossRayPairs I ray) : ray p.1 ≠ ray p.2 :=
  (Finset.mem_filter.mp hp).2

/-- In a cross-ray energy expansion the all-equal-ray family is absent. -/
theorem cross_quadruple_not_all_equal {ι : Type*} (I : Finset ι) (ray : ι → ℤ)
    (pr : (ι × ι) × (ι × ι))
    (hpr : pr ∈ crossRayPairs I ray ×ˢ crossRayPairs I ray) :
    ¬ (ray pr.1.1 = ray pr.1.2 ∧ ray pr.1.1 = ray pr.2.1 ∧
      ray pr.1.1 = ray pr.2.2) := by
  intro hall
  exact cross_pair_ray_ne I ray pr.1 (Finset.mem_product.mp hpr).1 hall.1

theorem balanced_cross_quadruple_not_all_equal {ι : Type*}
    (I : Finset ι) (ray radial : ι → ℤ) (pr : (ι × ι) × (ι × ι))
    (hpr : pr ∈ balancedQuadruples (crossRayPairs I ray) ray radial) :
    ¬ (ray pr.1.1 = ray pr.1.2 ∧ ray pr.1.1 = ray pr.2.1 ∧
      ray pr.1.1 = ray pr.2.2) :=
  cross_quadruple_not_all_equal I ray pr (Finset.mem_filter.mp hpr).1

/-- Two different same-ray pairs satisfying the frequency equations must
each be radially diagonal. -/
theorem same_ray_balance_forces_radial_diagonal {ι : Type*}
    (ray radial : ι → ℤ) (p r : ι × ι)
    (hp : ray p.1 = ray p.2) (hr : ray r.1 = ray r.2)
    (hne : ray p.1 ≠ ray r.1) (hb : frequencyBalance ray radial p r) :
    radial p.1 = radial p.2 ∧ radial r.1 = radial r.2 := by
  rcases hb with ⟨h₁, h₂⟩
  rw [← hp, ← hr] at h₂
  have hscaled := congrArg (fun z : ℤ => ray r.1 * z) h₁
  have hmul : (ray p.1 - ray r.1) * (radial p.1 - radial p.2) = 0 := by
    nlinarith
  have hrad := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  constructor <;> omega

/-- Taking every pair recovers the fourth power of the original finite sum. -/
theorem pairSum_all_pairs {α ι : Type*} (I : Finset ι) (f : ι → α → ℂ) (x : α) :
    pairSum (I ×ˢ I) f x =
      (∑ i ∈ I, f i x) * conj (∑ i ∈ I, f i x) := by
  simp only [pairSum, pairValue, Finset.sum_product, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem pairSum_all_pairs_norm_sq {α ι : Type*}
    (I : Finset ι) (f : ι → α → ℂ) (x : α) :
    ‖pairSum (I ×ˢ I) f x‖ ^ 2 = ‖∑ i ∈ I, f i x‖ ^ 4 := by
  rw [pairSum_all_pairs, norm_mul, Complex.norm_conj]
  ring

theorem integral_fourth_moment_le_balanced_card
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (I : Finset ι) (f : ι → α → ℂ) (ray radial : ι → ℤ)
    (B : ℝ) (hB : 0 ≤ B)
    (hi : ∀ p ∈ I ×ˢ I, ∀ r ∈ I ×ˢ I, Integrable (quarticKernel f p r) μ)
    (hzero : ∀ p ∈ I ×ˢ I, ∀ r ∈ I ×ˢ I, ¬ frequencyBalance ray radial p r →
      (∫ x, quarticKernel f p r x ∂μ) = 0)
    (hbound : ∀ p ∈ I ×ˢ I, ∀ r ∈ I ×ˢ I, frequencyBalance ray radial p r →
      ‖∫ x, quarticKernel f p r x ∂μ‖ ≤ B) :
    Integrable (fun x => ‖∑ i ∈ I, f i x‖ ^ 4) μ ∧
      (∫ x, ‖∑ i ∈ I, f i x‖ ^ 4 ∂μ) ≤
        B * (balancedQuadruples (I ×ˢ I) ray radial).card := by
  constructor
  · simpa only [pairSum_all_pairs_norm_sq] using integrable_pairSum_norm_sq μ (I ×ˢ I) f hi
  · simpa only [pairSum_all_pairs_norm_sq] using
      integral_pairSum_norm_sq_le_balanced_card μ (I ×ˢ I) f ray radial B hB hi hzero hbound

def weightedAtoms {α ι : Type*} (a : ι → ℂ) (f : ι → α → ℂ) (i : ι) (x : α) : ℂ :=
  a i * f i x

def pairCoefficient {ι : Type*} (a : ι → ℂ) (p : ι × ι) : ℂ := a p.1 * conj (a p.2)

def quarticCoefficient {ι : Type*} (a : ι → ℂ) (p r : ι × ι) : ℂ :=
  pairCoefficient a p * conj (pairCoefficient a r)

theorem pairCoefficient_norm_le_one {ι : Type*} (a : ι → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (p : ι × ι) : ‖pairCoefficient a p‖ ≤ 1 := by
  dsimp [pairCoefficient]
  rw [norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * 1 := mul_le_mul (ha p.1) (ha p.2) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem quarticCoefficient_norm_le_one {ι : Type*} (a : ι → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (p r : ι × ι) : ‖quarticCoefficient a p r‖ ≤ 1 := by
  dsimp [quarticCoefficient]
  rw [norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * 1 := mul_le_mul (pairCoefficient_norm_le_one a ha p)
      (pairCoefficient_norm_le_one a ha r) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem weighted_quarticKernel {α ι : Type*} (a : ι → ℂ) (f : ι → α → ℂ)
    (p r : ι × ι) (x : α) :
    quarticKernel (weightedAtoms a f) p r x =
      quarticCoefficient a p r * quarticKernel f p r x := by
  simp only [quarticKernel, pairValue, weightedAtoms, quarticCoefficient, pairCoefficient,
    map_mul]
  ring

theorem integral_weighted_quarticKernel
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (a : ι → ℂ) (f : ι → α → ℂ) (p r : ι × ι) :
    (∫ x, quarticKernel (weightedAtoms a f) p r x ∂μ) =
      quarticCoefficient a p r * ∫ x, quarticKernel f p r x ∂μ := by
  simp_rw [weighted_quarticKernel]
  exact integral_const_mul _ _

/-- Bounded complex coefficients preserve the same constrained counting bound.
No positivity of their quartic products is used. -/
theorem integral_weighted_pairSum_norm_sq_le_balanced_card
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : Finset (ι × ι)) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (f : ι → α → ℂ) (ray radial : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hi : ∀ p ∈ P, ∀ r ∈ P, Integrable (quarticKernel f p r) μ)
    (hzero : ∀ p ∈ P, ∀ r ∈ P, ¬ frequencyBalance ray radial p r →
      (∫ x, quarticKernel f p r x ∂μ) = 0)
    (hbound : ∀ p ∈ P, ∀ r ∈ P, frequencyBalance ray radial p r →
      ‖∫ x, quarticKernel f p r x ∂μ‖ ≤ B) :
    Integrable (fun x => ‖pairSum P (weightedAtoms a f) x‖ ^ 2) μ ∧
      (∫ x, ‖pairSum P (weightedAtoms a f) x‖ ^ 2 ∂μ) ≤
        B * (balancedQuadruples P ray radial).card := by
  have hi' : ∀ p ∈ P, ∀ r ∈ P, Integrable (quarticKernel (weightedAtoms a f) p r) μ := by
    intro p hp r hr
    have heq : quarticKernel (weightedAtoms a f) p r =
        fun x => quarticCoefficient a p r * quarticKernel f p r x :=
      funext (weighted_quarticKernel a f p r)
    rw [heq]
    exact (hi p hp r hr).const_mul _
  refine ⟨integrable_pairSum_norm_sq μ P (weightedAtoms a f) hi', ?_⟩
  apply integral_pairSum_norm_sq_le_balanced_card μ P (weightedAtoms a f) ray radial B hB hi'
  · intro p hp r hr hnot
    rw [integral_weighted_quarticKernel, hzero p hp r hr hnot, mul_zero]
  · intro p hp r hr hbal
    rw [integral_weighted_quarticKernel, norm_mul]
    calc
      _ ≤ 1 * ‖∫ x, quarticKernel f p r x ∂μ‖ :=
        mul_le_mul_of_nonneg_right (quarticCoefficient_norm_le_one a ha p r) (norm_nonneg _)
      _ ≤ B := by simpa using hbound p hp r hr hbal

/-- The exclusion applies equally to restricted cap-pair families, not just to
the complete cross-pair set. -/
theorem restricted_cross_quadruple_not_all_equal {ι : Type*}
    (P : Finset (ι × ι)) (ray : ι → ℤ)
    (hcross : ∀ p ∈ P, ray p.1 ≠ ray p.2)
    (pr : (ι × ι) × (ι × ι)) (hpr : pr ∈ P ×ˢ P) :
    ¬ (ray pr.1.1 = ray pr.1.2 ∧ ray pr.1.1 = ray pr.2.1 ∧
      ray pr.1.1 = ray pr.2.2) := by
  intro hall
  exact hcross pr.1 (Finset.mem_product.mp hpr).1 hall.1

def cutoffAtoms {α ι : Type*} (χ : α → ℂ) (f : ι → α → ℂ) (i : ι) (x : α) : ℂ :=
  χ x * f i x

/-- The common cutoff is exactly `|χ|⁴` in every expanded quartic term. -/
theorem common_cutoff_quarticKernel {α ι : Type*}
    (χ : α → ℂ) (f : ι → α → ℂ) (p r : ι × ι) (x : α) :
    quarticKernel (cutoffAtoms χ f) p r x =
      ((‖χ x‖ ^ 4 : ℝ) : ℂ) * quarticKernel f p r x := by
  have hz : χ x * conj (χ x) = ((‖χ x‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj (χ x)
  calc
    _ = (χ x * conj (χ x)) ^ 2 * quarticKernel f p r x := by
      simp [quarticKernel, pairValue, cutoffAtoms, map_mul]
      ring
    _ = _ := by
      rw [hz]
      push_cast
      ring

theorem integral_weighted_fourth_moment_le_balanced_card
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (I : Finset ι) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (f : ι → α → ℂ) (ray radial : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hi : ∀ p ∈ I ×ˢ I, ∀ r ∈ I ×ˢ I, Integrable (quarticKernel f p r) μ)
    (hzero : ∀ p ∈ I ×ˢ I, ∀ r ∈ I ×ˢ I, ¬ frequencyBalance ray radial p r →
      (∫ x, quarticKernel f p r x ∂μ) = 0)
    (hbound : ∀ p ∈ I ×ˢ I, ∀ r ∈ I ×ˢ I, frequencyBalance ray radial p r →
      ‖∫ x, quarticKernel f p r x ∂μ‖ ≤ B) :
    Integrable (fun x => ‖∑ i ∈ I, a i * f i x‖ ^ 4) μ ∧
      (∫ x, ‖∑ i ∈ I, a i * f i x‖ ^ 4 ∂μ) ≤
        B * (balancedQuadruples (I ×ˢ I) ray radial).card := by
  simpa only [pairSum_all_pairs_norm_sq, weightedAtoms] using
    integral_weighted_pairSum_norm_sq_le_balanced_card μ (I ×ˢ I) a ha f ray radial B hB
      hi hzero hbound

end

end CircleDivisor.FourierEnergy
