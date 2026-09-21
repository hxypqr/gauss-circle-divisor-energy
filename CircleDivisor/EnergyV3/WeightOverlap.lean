import CircleDivisor.GuthMaldagueInput

/-! Uniform bounded overlap of the actual product-decay weights. The proof
first handles the integer lattice in one dimension, then bounds arbitrary
finite subsets of the three-dimensional lattice. -/

namespace CircleDivisor.EnergyV3.WeightOverlap
noncomputable section
open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 1200000

def weight (x : ℝ) : ℝ := ((1 + x ^ 2) ^ 100)⁻¹

theorem weight_nonneg (x : ℝ) : 0 ≤ weight x := by unfold weight; positivity

theorem weight_antitone_sq {x y : ℝ} (h : x ^ 2 ≤ y ^ 2) : weight y ≤ weight x := by
  unfold weight
  apply inv_anti₀ (by positivity)
  gcongr

theorem weight_le_one_div_sq (x : ℝ) (hx : x ≠ 0) : weight x ≤ 1 / x ^ 2 := by
  have hp := le_self_pow₀ (show (1 : ℝ) ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x]) (show 100 ≠ 0 by decide)
  unfold weight
  rw [one_div]
  apply inv_anti₀ (sq_pos_of_ne_zero hx)
  linarith

theorem weight_le_one (x : ℝ) : weight x ≤ 1 := by
  unfold weight
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith [sq_nonneg x]))

def majorant (n : ℤ) : ℝ := (if n = 0 then 1 else 0) + 1 / (n : ℝ) ^ 2

theorem majorant_nonneg (n : ℤ) : 0 ≤ majorant n := by unfold majorant; positivity

theorem majorant_summable : Summable majorant := by
  unfold majorant
  apply Summable.add
  · exact summable_of_ne_finset_zero (s := {0}) (by intro n hn; simp_all)
  · exact Real.summable_one_div_int_pow.mpr (by norm_num)

theorem weight_le_majorant (n : ℤ) : weight n ≤ majorant n := by
  by_cases hn : n = 0
  · simp [hn, weight, majorant]
  · simpa [majorant, hn] using weight_le_one_div_sq (n : ℝ) (by exact_mod_cast hn)

def overlapConstant : ℝ := ∑' n : ℤ, majorant n

theorem overlapConstant_nonneg : 0 ≤ overlapConstant := tsum_nonneg majorant_nonneg

/-- Rounding the center leaves an error at most 1/2. Integer separation then
dominates every nonzero translated index, with an absolute factor two. -/
theorem shifted_distance (v : ℝ) (m : ℤ) :
    |(m : ℝ)| ≤ 2 * |v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ)| := by
  by_cases hm : m = 0
  · simp [hm]
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
  have hfloor := Int.floor_le (v + 1 / 2)
  have hfloor' := Int.lt_floor_add_one (v + 1 / 2)
  have herr : |v - (⌊v + 1 / 2⌋ : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have htri := abs_add_le
    ((⌊v + 1 / 2⌋ : ℝ) + m - v) (v - (⌊v + 1 / 2⌋ : ℝ))
  rw [show (⌊v + 1 / 2⌋ : ℝ) + m - v + (v - (⌊v + 1 / 2⌋ : ℝ)) = m by ring] at htri
  rw [show (⌊v + 1 / 2⌋ : ℝ) + m - v = -(v - ((⌊v + 1 / 2⌋ : ℝ) + m)) by ring,
    abs_neg] at htri
  push_cast
  linarith

theorem shifted_weight_le (v : ℝ) (m : ℤ) :
    weight (v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ)) ≤ 4 * majorant m := by
  by_cases hm : m = 0
  · have hw := weight_le_one (v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ))
    simp [hm, majorant] at *
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hd := shifted_distance v m
  have hmpos := abs_pos.mpr hm0
  have hx : v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ) ≠ 0 := by
    intro heq
    rw [heq, abs_zero, mul_zero] at hd
    linarith
  have hs : (m : ℝ) ^ 2 ≤ 4 * (v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ)) ^ 2 := by
    nlinarith [abs_nonneg (v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ)), sq_abs (m : ℝ),
      sq_abs (v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ))]
  have hi : 1 / (v - ((⌊v + 1 / 2⌋ + m : ℤ) : ℝ)) ^ 2 ≤ 4 / (m : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hx) (sq_pos_of_ne_zero hm0)).mpr
    nlinarith
  simpa [majorant, hm, div_eq_mul_inv] using (weight_le_one_div_sq _ hx).trans hi

theorem finite_shifted_sum (I : Finset ℤ) (v : ℝ) :
    ∑ n ∈ I, weight (v - n) ≤ 4 * overlapConstant := by
  classical
  let k : ℤ := ⌊v + 1 / 2⌋
  let f : ℤ → ℝ := fun m => weight (v - ((k + m : ℤ) : ℝ))
  have hf : Summable f := (majorant_summable.mul_left 4).of_nonneg_of_le
    (fun _ => weight_nonneg _) (shifted_weight_le v)
  have hs : Summable (fun n : ℤ => weight (v - n)) := (Equiv.addLeft k).summable_iff.mp hf
  calc
    _ ≤ ∑' n : ℤ, weight (v - n) := hs.sum_le_tsum I (fun _ _ => weight_nonneg _)
    _ = ∑' m : ℤ, f m := (Equiv.addLeft k).tsum_eq (fun n : ℤ => weight (v - n)) |>.symm
    _ ≤ ∑' m : ℤ, 4 * majorant m := hf.tsum_le_tsum (shifted_weight_le v) (majorant_summable.mul_left 4)
    _ = 4 * overlapConstant := by rw [tsum_mul_left]; rfl

theorem finite_product_shifted_sum {d : Type*} [Fintype d] (I : Finset (d → ℤ)) (v : d → ℝ) :
    ∑ m ∈ I, ∏ k, weight (v k - m k) ≤ (4 * overlapConstant) ^ Fintype.card d := by
  classical
  let J : d → Finset ℤ := fun k => I.image (fun m => m k)
  have hsub : I ⊆ Fintype.piFinset J := by
    intro m hm
    simp only [Fintype.mem_piFinset]
    intro k
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  calc
    _ ≤ ∑ m ∈ Fintype.piFinset J, ∏ k, weight (v k - m k) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ =>
        Finset.prod_nonneg (fun _ _ => weight_nonneg _))
    _ = ∏ k, ∑ n ∈ J k, weight (v k - n) :=
      (Finset.prod_univ_sum J (fun k (n : ℤ) => weight (v k - n))).symm
    _ ≤ ∏ _k : d, (4 * overlapConstant) := by
      apply Finset.prod_le_prod
      · intro k _
        exact Finset.sum_nonneg (fun _ _ => weight_nonneg _)
      · intro k _
        exact finite_shifted_sum (J k) (v k)
    _ = (4 * overlapConstant) ^ Fintype.card d := by simp

open GuthMaldague in
theorem actual_envelope_finite_overlap (n j : ℕ) (i : CapIndex j)
    (I : Finset Lattice) (x : Space) :
    ∑ m ∈ I, envelopeWeight n j i m x ≤ (4 * overlapConstant) ^ 3 / weightNormalization := by
  have heq (m : Lattice) : envelopeWeight n j i m x =
      (∏ k : Fin 3, weight (envelopeCoordinates (radius n) (scale j) (leftEndpoint j i) x k - m k)) /
        weightNormalization := by
    simp only [envelopeWeight, normalizedWeight, baseWeight, weight, envelopeCoordinates_sub,
      envelopeCenter, envelopeCoordinates_synthesis _ _ _ (radius_pos n).ne' (scale_pos j).ne']
  simp_rw [heq]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ weightNormalization_pos.le
  simpa using finite_product_shifted_sum I (envelopeCoordinates (radius n) (scale j) (leftEndpoint j i) x)

open GuthMaldague in
theorem actual_envelope_overlap (n j : ℕ) (i : CapIndex j) (x : Space) :
    Summable (fun m : Lattice => envelopeWeight n j i m x) ∧
    (∑' m : Lattice, envelopeWeight n j i m x) ≤
      (4 * overlapConstant) ^ 3 / weightNormalization := by
  have hnn : 0 ≤ (fun m : Lattice => envelopeWeight n j i m x) :=
    fun m => envelopeWeight_nonneg n j i m x
  exact ⟨summable_of_sum_le hnn (fun I => actual_envelope_finite_overlap n j i I x),
    Real.tsum_le_of_sum_le hnn (fun I => actual_envelope_finite_overlap n j i I x)⟩

end
end CircleDivisor.EnergyV3.WeightOverlap
