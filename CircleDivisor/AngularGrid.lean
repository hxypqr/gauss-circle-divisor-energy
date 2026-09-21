import Mathlib

/-! Exact two-grid separation used by Lemma 2.1. Angles are lifted to the real
line; the statements include the wraparound boundary since all integer cells occur. -/

namespace CircleDivisor.AngularGrid
noncomputable section

def offset (b : Bool) : ℝ := if b then 1 / 2 else 0

theorem safe_grid_unit (x : ℝ) :
    ∃ b : Bool, ∀ n : ℤ, (1 / 4 : ℝ) ≤ |x - ((n : ℝ) + offset b)| := by
  let k : ℤ := ⌊x⌋
  have hk : (k : ℝ) ≤ x := Int.floor_le x
  have hk' : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  by_cases hlo : (k : ℝ) + 1 / 4 ≤ x
  · by_cases hhi : x ≤ (k : ℝ) + 3 / 4
    · refine ⟨false, fun n => ?_⟩
      dsimp [offset]
      rcases le_or_gt n k with hn | hn
      · have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have hn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
        rw [abs_of_nonpos (by linarith)]
        linarith
    · refine ⟨true, fun n => ?_⟩
      dsimp [offset]
      rcases le_or_gt n k with hn | hn
      · have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have hn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
        rw [abs_of_nonpos (by linarith)]
        linarith
  · refine ⟨true, fun n => ?_⟩
    dsimp [offset]
    rcases lt_or_ge n k with hn | hn
    · have hn' : (n : ℝ) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hn' : (k : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_nonpos (by linarith)]
      linarith

/-- Every ray can be assigned wholly to one of two half-cell shifted grids. -/
theorem safe_grid (δ x : ℝ) (hδ : 0 < δ) :
    ∃ b : Bool, ∀ n : ℤ, δ / 4 ≤ |x - δ * ((n : ℝ) + offset b)| := by
  obtain ⟨b, hb⟩ := safe_grid_unit (x / δ)
  refine ⟨b, fun n => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hb n) hδ.le
  have hid : x - δ * ((n : ℝ) + offset b) = δ * (x / δ - ((n : ℝ) + offset b)) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hδ]
  linarith

/-- The safe grid retains every point in an entire atom of radius δ/8. -/
theorem same_cell_of_safe_grid (δ x y : ℝ) (hδ : 0 < δ) (b : Bool)
    (hsafe : ∀ n : ℤ, δ / 4 ≤ |x - δ * ((n : ℝ) + offset b)|)
    (hnear : |y - x| < δ / 8) :
    ⌊y / δ - offset b⌋ = ⌊x / δ - offset b⌋ := by
  let n : ℤ := ⌊x / δ - offset b⌋
  have hl := Int.floor_le (x / δ - offset b)
  have hu := Int.lt_floor_add_one (x / δ - offset b)
  change (n : ℝ) ≤ x / δ - offset b at hl
  change x / δ - offset b < (n : ℝ) + 1 at hu
  have hxlo : δ * ((n : ℝ) + offset b) ≤ x := by
    have hh : (n : ℝ) + offset b ≤ x / δ := by linarith
    simpa only [mul_comm] using (le_div_iff₀ hδ).mp hh
  have hxhi : x < δ * ((n : ℝ) + 1 + offset b) := by
    have hh : x / δ < (n : ℝ) + 1 + offset b := by linarith
    have := (div_lt_iff₀ hδ).mp hh
    nlinarith
  have hlo := hsafe n
  rw [abs_of_nonneg (by linarith : 0 ≤ x - δ * ((n : ℝ) + offset b))] at hlo
  have hhi := hsafe (n + 1)
  simp only [Int.cast_add, Int.cast_one] at hhi
  rw [abs_of_nonpos (by linarith : x - δ * ((n : ℝ) + 1 + offset b) ≤ 0)] at hhi
  rw [abs_lt] at hnear
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  · apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hδ).mpr
    nlinarith

end
end CircleDivisor.AngularGrid
