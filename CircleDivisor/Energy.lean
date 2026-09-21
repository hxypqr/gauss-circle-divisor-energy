import Mathlib

/-!
# Signed amplitude splitting and energy bounds

Internal lemmas of Sections 3–4. These results have no external analytic assumptions.
In particular the cross-ray quantity is real and may be negative.
-/

namespace CircleDivisor.Energy

/-- The restricted square appearing in (4.1). -/
noncomputable def restrictedSquare (x u : ℝ) : ℝ := if u ≤ x then x ^ 2 else 0

theorem restrictedSquare_nonneg (x u : ℝ) : 0 ≤ restrictedSquare x u := by
  unfold restrictedSquare
  split_ifs <;> positivity

/-- Lemma 4.1, including the sign issue for the cross-ray term. -/
theorem restricted_splitting {M D C u : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (h : M = D + C) (_hu : 0 < u) :
    restrictedSquare M u ≤
      4 * restrictedSquare D (u / 2) + 4 * restrictedSquare |C| (u / 2) := by
  by_cases hMu : u ≤ M
  · have hsum : M ≤ D + |C| := by rw [h]; exact add_le_add_right (le_abs_self C) D
    have hhalf : M / 2 ≤ D ∨ M / 2 ≤ |C| := by by_contra! hn; linarith
    rcases hhalf with hd | hc
    · have hDu : u / 2 ≤ D := by linarith
      have hsq : M ^ 2 ≤ 4 * D ^ 2 := by nlinarith
      simpa [restrictedSquare, hMu, hDu] using
        hsq.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num)
          (restrictedSquare_nonneg |C| (u / 2))))
    · have hCu : u / 2 ≤ |C| := by linarith
      have hsq : M ^ 2 ≤ 4 * |C| ^ 2 := by nlinarith [abs_nonneg C]
      simpa [restrictedSquare, hMu, hCu] using
        hsq.trans (le_add_of_nonneg_left (mul_nonneg (by norm_num)
          (restrictedSquare_nonneg D (u / 2))))
  · simp only [restrictedSquare, if_neg hMu]
    positivity

/-- The threshold in (2.9) implies two distinct amplitude cutoffs. -/
theorem split_with_separate_cutoffs {M D C d b u : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (h : M = D + C) (hu : 0 < u)
    (hd : D ≤ d) (hb : |C| ≤ b) :
    restrictedSquare M u ≤
      (if u / 2 ≤ d then 4 * D ^ 2 else 0) +
      (if u / 2 ≤ b then 4 * |C| ^ 2 else 0) := by
  apply (restricted_splitting hM hD h hu).trans
  apply add_le_add
  · unfold restrictedSquare
    split_ifs <;> nlinarith
  · unfold restrictedSquare
    split_ifs <;> nlinarith

/-- The elementary estimate used in (3.11), valid for signed `C`. -/
theorem cross_square_le {M D C : ℝ} (h : C = M - D) :
    |C| ^ 2 ≤ 2 * M ^ 2 + 2 * D ^ 2 := by
  rw [sq_abs, h]
  nlinarith [sq_nonneg (M + D)]

theorem cross_abs_le {M D C : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (h : C = M - D) : |C| ≤ M + D := by
  rw [h, abs_le]
  constructor <;> linarith

/-- Local upper bound times first moment bounds a finite energy. -/
theorem energy_le_density {ι : Type*} (I : Finset ι) (w f : ι → ℝ) (B : ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hf : ∀ i ∈ I, 0 ≤ f i)
    (hB : ∀ i ∈ I, f i ≤ B) :
    ∑ i ∈ I, w i * (f i) ^ 2 ≤ B * ∑ i ∈ I, w i * f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hmul := mul_le_mul_of_nonneg_left (hB i hi) (hf i hi)
  have hmul' := mul_le_mul_of_nonneg_left hmul (hw i hi)
  nlinarith

/-- The finite version of the signed cross-energy estimate in (3.11). -/
theorem cross_energy_le {ι : Type*} (I : Finset ι) (w M D : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    ∑ i ∈ I, w i * |M i - D i| ^ 2 ≤
      2 * (∑ i ∈ I, w i * (M i) ^ 2) +
      2 * (∑ i ∈ I, w i * (D i) ^ 2) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hh := mul_le_mul_of_nonneg_left (cross_square_le (M := M i) (D := D i) rfl)
    (hw i hi)
  nlinarith

/-- The branchwise square cutoff is retained after summing envelopes. -/
theorem sum_split_with_separate_cutoffs {ι : Type*} (I : Finset ι)
    (w M D C : ι → ℝ) (d b u : ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hM : ∀ i ∈ I, 0 ≤ M i)
    (hD : ∀ i ∈ I, 0 ≤ D i) (h : ∀ i ∈ I, M i = D i + C i)
    (hu : 0 < u) (hd : ∀ i ∈ I, D i ≤ d) (hb : ∀ i ∈ I, |C i| ≤ b) :
    ∑ i ∈ I, w i * restrictedSquare (M i) u ≤
      (if u / 2 ≤ d then 4 * ∑ i ∈ I, w i * (D i) ^ 2 else 0) +
      (if u / 2 ≤ b then 4 * ∑ i ∈ I, w i * |C i| ^ 2 else 0) := by
  calc
    _ ≤ ∑ i ∈ I, w i * ((if u / 2 ≤ d then 4 * (D i) ^ 2 else 0) +
        (if u / 2 ≤ b then 4 * |C i| ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (split_with_separate_cutoffs (hM i hi) (hD i hi) (h i hi) hu (hd i hi) (hb i hi))
        (hw i hi)
    _ = _ := by
      split_ifs <;> simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_comm, mul_assoc]

end CircleDivisor.Energy
