import CircleDivisor.Statements

/-! Finiteness and the actual squared-radius domain in the main specification. -/

namespace CircleDivisor

theorem circle_coordinate_bound {x y X : ℝ} (h : x ^ 2 + y ^ 2 ≤ X) :
    |x| ≤ |X| + 1 := by
  have hx := sq_abs x
  have hX := le_abs_self X
  have hy := sq_nonneg y
  have hpos := abs_nonneg X
  have habs := abs_nonneg x
  nlinarith [sq_nonneg (|x| - (|X| + 1))]

theorem circle_lattice_set_finite (X : ℝ) :
    Set.Finite {p : ℤ × ℤ | (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ X} := by
  let B : ℤ := ⌈|X| + 1⌉
  have hB : |X| + 1 ≤ (B : ℝ) := Int.le_ceil _
  apply ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).subset
  intro p hp
  change (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ X at hp
  have hp₁ := (circle_coordinate_bound hp).trans hB
  have hp₂ := (circle_coordinate_bound (x := (p.2 : ℝ)) (y := p.1) (by linarith)).trans hB
  rw [abs_le] at hp₁ hp₂
  change (-B ≤ p.1 ∧ p.1 ≤ B) ∧ (-B ≤ p.2 ∧ p.2 ≤ B)
  norm_cast at hp₁ hp₂

theorem circle_lattice_set_empty {X : ℝ} (hX : X < 0) :
    {p : ℤ × ℤ | (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ X} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2 : ℝ)]

theorem circleCount_mono : Monotone circleCount := by
  intro X Y hXY
  unfold circleCount
  apply Set.ncard_le_ncard _ (circle_lattice_set_finite Y)
  intro p hp
  exact hp.trans hXY

end CircleDivisor
