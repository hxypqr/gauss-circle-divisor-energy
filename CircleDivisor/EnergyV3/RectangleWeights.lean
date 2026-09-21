import CircleDivisor.EnergyV3.ReductionReciprocal

namespace CircleDivisor.EnergyV3
noncomputable section
open scoped BigOperators
open ExternalInterfaces

def upperCutoff (t x : ℝ) : ℂ := if x < t then 1 else 0

theorem upperCutoff_BV (t : ℝ) : BVControl 1 (upperCutoff t) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold upperCutoff
    split_ifs <;> norm_num
  · let f : ℝ → ℝ := fun x => if x < t then 0 else 1
    have hmono : Monotone f := by
      intro x y hxy
      dsimp [f]
      split_ifs <;> norm_num <;> linarith
    have hvar := (hmono.monotoneOn Set.univ).eVariationOn_le
      (a := (1 : ℝ)) (b := 2) (by trivial) (by trivial)
    simp only [Set.univ_inter] at hvar
    have hf1 : f 2 - f 1 ≤ 1 := by dsimp [f]; split_ifs <;> norm_num
    have hL : LipschitzOnWith 1 (fun r : ℝ => (1 : ℂ) - (r : ℂ)) Set.univ := by
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      rw [show (1 : ℂ) - x - (1 - y) = -((x : ℂ) - y) by ring,
        norm_neg, ← Complex.ofReal_sub, Complex.norm_real]
    have hc := hL.comp_eVariationOn_le
      (g := f) (s := Set.Icc (1 : ℝ) 2) (fun x hx => Set.mem_univ _)
    have heq : upperCutoff t = (fun r : ℝ => (1 : ℂ) - (r : ℂ)) ∘ f := by
      ext x
      simp only [upperCutoff, Function.comp_apply, f]
      split_ifs <;> norm_num
    rw [← heq] at hc
    simp only [ENNReal.coe_one, one_mul] at hc
    exact hc.trans (hvar.trans (ENNReal.ofReal_le_ofReal hf1))

theorem sum_int_Ico_eq_nat (lo hi : ℕ) (f : ℤ → ℂ) :
    (∑ z ∈ Finset.Ico (lo : ℤ) hi, f z) = ∑ n ∈ Finset.Ico lo hi, f n := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    exact_mod_cast hn
  · intro n hn m hm hnm
    exact_mod_cast hnm
  · intro z hz
    have hz0 : 0 ≤ z := (Int.natCast_nonneg lo).trans (Finset.mem_Ico.mp hz).1
    refine ⟨z.toNat, ?_, Int.toNat_of_nonneg hz0⟩
    simp only [Finset.mem_Ico] at hz ⊢
    omega
  · intro n hn
    rfl

theorem sum_dyadic_upperCutoff (H V : ℕ) (hH : 1 ≤ H) (hHV : H ≤ V) (hVH : V ≤ 2 * H)
    (f : ℤ → ℂ) :
    (∑ h ∈ dyadicIntegers H, upperCutoff ((V : ℝ) / H) ((h : ℝ) / H) * f h) =
      ∑ h ∈ Finset.Ico H V, f h := by
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hd : dyadicIntegers H = Finset.Ico (H : ℤ) (2 * H : ℕ) := by
    unfold dyadicIntegers
    have heq : (2 : ℝ) * H = ((2 * H : ℕ) : ℝ) := by push_cast; ring
    rw [heq, Int.ceil_natCast, Int.ceil_natCast]
  rw [hd, sum_int_Ico_eq_nat]
  symm
  calc
    _ = ∑ h ∈ Finset.Ico H V,
        upperCutoff ((V : ℝ) / H) ((h : ℝ) / H) * f h := by
      apply Finset.sum_congr rfl
      intro h hh
      have hlt : (h : ℝ) / H < V / H :=
        (div_lt_div_iff_of_pos_right hHr).mpr (by exact_mod_cast (Finset.mem_Ico.mp hh).2)
      simp [upperCutoff, hlt]
    _ = _ := by
      apply Finset.sum_subset
      · intro h hh
        simp only [Finset.mem_Ico] at hh ⊢
        omega
      · intro h hh hnot
        have hge : V ≤ h := by
          simp only [Finset.mem_Ico] at hh hnot
          omega
        have hnlt : ¬(h : ℝ) / H < V / H := by
          rw [not_lt, div_le_div_iff_of_pos_right hHr]
          exact_mod_cast hge
        simp [upperCutoff, hnlt]

theorem reciprocalSum_upperCutoffs (H M n V : ℕ)
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hn : n ≤ H) (hMV : M ≤ V) (hVM : V ≤ 2 * M)
    (T : ℝ) (F : ℝ → ℝ) :
    reciprocalSum H M T F
      (upperCutoff (((H + n : ℕ) : ℝ) / H)) (upperCutoff ((V : ℝ) / M)) =
      ∑ i ∈ Finset.range n, frequencySum (Finset.Ico M V)
        (fun m : ℕ => (T / M) * F ((m : ℝ) / M)) (H + i) := by
  unfold reciprocalSum
  have hg : ∀ h : ℤ,
      (∑ m ∈ dyadicIntegers M,
        upperCutoff (((H + n : ℕ) : ℝ) / H) ((h : ℝ) / H) *
          upperCutoff ((V : ℝ) / M) ((m : ℝ) / M) *
            exponential ((h * T / M) * F (m / M))) =
      upperCutoff (((H + n : ℕ) : ℝ) / H) ((h : ℝ) / H) *
        (∑ m ∈ Finset.Ico M V, exponential ((h * T / M) * F (m / M))) := by
    intro h
    rw [Finset.mul_sum]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    exact sum_dyadic_upperCutoff M V hM hMV hVM _
  simp_rw [hg]
  rw [sum_dyadic_upperCutoff H (H + n) hH (by omega) (by omega),
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i hi
  unfold frequencySum
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  push_cast
  ring

end
end CircleDivisor.EnergyV3
