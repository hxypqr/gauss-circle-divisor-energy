import CircleDivisor.ClassicalInputs
import Mathlib.Data.Nat.Log

/-! Exact finite dyadic partitions, including the last truncated block. -/

namespace CircleDivisor.EnergyV3
noncomputable section
open scoped BigOperators

def dyadicBlock (Y j : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (Y + 1))

theorem dyadicBlock_eq_min (Y j : ℕ) :
    dyadicBlock Y j = Finset.Ico (min (2 ^ j) (Y + 1))
      (min (2 ^ (j + 1)) (Y + 1)) := by
  ext h
  simp only [dyadicBlock, Finset.mem_Ico, lt_min_iff, min_le_iff]
  omega

theorem dyadic_partition_partial {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (Y N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ h ∈ dyadicBlock Y j, f h) =
      ∑ h ∈ Finset.Ico 1 (min (2 ^ N) (Y + 1)), f h := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, dyadicBlock_eq_min]
    apply Finset.sum_Ico_consecutive
    · exact le_min (Nat.one_le_pow _ _ (by omega)) (by omega)
    · apply min_le_min_right
      exact Nat.pow_le_pow_right (by omega) (by omega)

theorem dyadic_partition {A : Type*} [AddCommMonoid A] (f : ℕ → A) (Y : ℕ) :
    (∑ j ∈ Finset.range (Nat.log 2 Y + 1), ∑ h ∈ dyadicBlock Y j, f h) =
      ∑ h ∈ Finset.Icc 1 Y, f h := by
  rw [dyadic_partition_partial, min_eq_right (Nat.lt_pow_succ_log_self (by omega) Y)]
  rfl

theorem dyadic_block_start_le (Y j : ℕ) (hY : 1 ≤ Y) (hj : j ≤ Nat.log 2 Y) :
    2 ^ j ≤ Y := Nat.pow_le_of_le_log (by omega) hj

theorem norm_sum_le_dyadic {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E) (Y : ℕ) (B : ℕ → ℝ)
    (hblock : ∀ j ≤ Nat.log 2 Y, ‖∑ h ∈ dyadicBlock Y j, f h‖ ≤ B j) :
    ‖∑ h ∈ Finset.Icc 1 Y, f h‖ ≤ ∑ j ∈ Finset.range (Nat.log 2 Y + 1), B j := by
  rw [← dyadic_partition]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun j hj => hblock j (by
    have := Finset.mem_range.mp hj
    omega))

theorem norm_sum_le_dyadic_constant {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E) (Y : ℕ) (B : ℝ)
    (hblock : ∀ j ≤ Nat.log 2 Y, ‖∑ h ∈ dyadicBlock Y j, f h‖ ≤ B) :
    ‖∑ h ∈ Finset.Icc 1 Y, f h‖ ≤ (Nat.log 2 Y + 1) * B := by
  simpa using norm_sum_le_dyadic f Y (fun _ => B) hblock

theorem sum_dyadic_starts (N : ℕ) :
    (∑ j ∈ Finset.range N, (2 : ℝ) ^ j) = (2 : ℝ) ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem sum_dyadic_starts_le (Y : ℕ) (hY : 1 ≤ Y) :
    (∑ j ∈ Finset.range (Nat.log 2 Y + 1), (2 : ℝ) ^ j) ≤ 2 * Y := by
  rw [sum_dyadic_starts, pow_succ]
  have hpow : (2 : ℝ) ^ Nat.log 2 Y ≤ (Y : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : Y ≠ 0)
  linarith

end
end CircleDivisor.EnergyV3
