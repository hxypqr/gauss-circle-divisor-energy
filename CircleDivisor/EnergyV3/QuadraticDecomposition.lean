import CircleDivisor.FourierEnergy

/-! A grouped quadratic polynomial is an actual sum of squared norms. This
justifies positivity of the same-ray part with arbitrary complex coefficients. -/

namespace CircleDivisor.EnergyV3.QuadraticDecomposition
noncomputable section
open FourierEnergy
open scoped ComplexConjugate BigOperators

theorem grouped_pairSum {α ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (c : ι → β) (f : ι → α → ℂ) (x : α) :
    pairSum ((I ×ˢ I).filter (fun p => c p.1 = c p.2)) f x =
      ∑ b ∈ I.image c, ((‖∑ k ∈ I.filter (fun k => c k = b), f k x‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hfib (b : β) : ((‖∑ k ∈ I.filter (fun k => c k = b), f k x‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ I ×ˢ I, if c p.1 = b ∧ c p.2 = b then pairValue f p x else 0 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, ← pairSum_all_pairs]
    simp only [pairSum, Finset.sum_product, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hca : c a = b <;> simp [hca]
  simp_rw [hfib]
  rw [Finset.sum_comm]
  unfold pairSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 : p.1 ∈ I := (Finset.mem_product.mp hp).1
  have him : c p.1 ∈ I.image c := Finset.mem_image_of_mem c hp1
  rw [Finset.sum_eq_single (c p.1)]
  · by_cases hc : c p.1 = c p.2 <;> simp [hc, eq_comm]
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot him).elim

theorem grouped_pairSum_real_nonneg {α ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (c : ι → β) (f : ι → α → ℂ) (x : α) :
    (pairSum ((I ×ˢ I).filter (fun p => c p.1 = c p.2)) f x).im = 0 ∧
    0 ≤ (pairSum ((I ×ˢ I).filter (fun p => c p.1 = c p.2)) f x).re := by
  rw [grouped_pairSum]
  simp only [Complex.re_sum, Complex.im_sum, Complex.ofReal_im, Complex.ofReal_re,
    Finset.sum_const_zero, true_and]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem pairSum_split {α ι : Type*} (P : Finset (ι × ι))
    (same : ι × ι → Prop) [DecidablePred same] (f : ι → α → ℂ) (x : α) :
    pairSum P f x = pairSum (P.filter same) f x + pairSum (P.filter (fun p => ¬same p)) f x := by
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end
end CircleDivisor.EnergyV3.QuadraticDecomposition
