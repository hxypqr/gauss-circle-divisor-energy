import CircleDivisor.ConeGeometry

/-! Explicit transposed-envelope metric in Appendix A.5.  The matrix below is
the physical transpose of the unscaled circular-cone map applied to the
generator, tangent and normal frame.  Fixed normalization factors can be
restored by scalar multiplication. -/
namespace CircleDivisor.EnergyV3.AdaptedMetric
noncomputable section
open scoped Matrix
abbrev Space := Fin 3 → ℝ

def envelopeMatrix (P s t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![P*s^2/(1+t^2), -2*P*s*t/(1+t^2), -P*t^2/(1+t^2);
     2*P*s^2*t/(1+t^2), 2*P*s*(1-t^2)/(1+t^2), 2*P*t/(1+t^2);
     P*s^2*t^2/(1+t^2), 2*P*s*t/(1+t^2), -P/(1+t^2)]

def dualCoordinates (P s t : ℝ) (v : Space) : Space :=
  (envelopeMatrix P s t).transpose.mulVec v

def circularMapMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; -1/2, 0, 1/2; 1/2, 0, 1/2]

def circularEnvelopeMatrix (P s t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*P*s^2*t/(1+t^2), -2*P*s*(t^2-1)/(1+t^2), 2*P*t/(1+t^2);
     P*s^2*(t^2-1)/(1+t^2), 4*P*s*t/(1+t^2), P*(t^2-1)/(1+t^2);
     P*s^2, 0, -P]

/-- Thus the metric is computed with the physical transpose, in the direction
required by the Fourier change of variables. -/
theorem envelopeMatrix_eq_physical_transpose (P s t : ℝ) :
    envelopeMatrix P s t = circularMapMatrix.transpose * circularEnvelopeMatrix P s t := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [envelopeMatrix, circularMapMatrix, circularEnvelopeMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> ring

theorem dualCoordinates_adapted (P s t : ℝ) (v : Space) :
    dualCoordinates P s t v =
      ![P*s^2*((1+t^2)*ConeGeometry.adapted t v 0 +
          2*t*ConeGeometry.adapted t v 1 + t^2/(1+t^2)*ConeGeometry.adapted t v 2),
        2*P*s*(ConeGeometry.adapted t v 1 + t/(1+t^2)*ConeGeometry.adapted t v 2),
        -P/(1+t^2)*ConeGeometry.adapted t v 2] := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  ext i
  fin_cases i <;> simp [dualCoordinates, envelopeMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, ConeGeometry.adapted] <;> field_simp <;> ring

theorem adapted_inverse_coordinates {P s t : ℝ} (hP : P ≠ 0) (hs : s ≠ 0) (v : Space) :
    let y := dualCoordinates P s t v
    P*s^2*ConeGeometry.adapted t v 0 =
      (y 0 - s*t*y 1 - s^2*t^2*y 2)/(1+t^2) ∧
    P*s*ConeGeometry.adapted t v 1 = y 1/2 + s*t*y 2 ∧
    P*ConeGeometry.adapted t v 2 = -(1+t^2)*y 2 := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  dsimp only
  rw [dualCoordinates_adapted]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.head_fin_const]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The norm of the *actual transpose-matrix image* controls each weighted
adapted coordinate, uniformly for the fixed positive cone arc. -/
theorem transpose_controls_adapted {P s t : ℝ} (hP : 0 < P) (hs : 0 < s)
    (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (v : Space) :
    P*s^2*|ConeGeometry.adapted t v 0| ≤ 9 * ‖dualCoordinates P s t v‖ ∧
    P*s*|ConeGeometry.adapted t v 1| ≤ 3 * ‖dualCoordinates P s t v‖ ∧
    P*|ConeGeometry.adapted t v 2| ≤ 5 * ‖dualCoordinates P s t v‖ := by
  let y := dualCoordinates P s t v
  have hy (i : Fin 3) : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hn : 0 ≤ ‖y‖ := norm_nonneg _
  have ht : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have ht5 : 1 + t ^ 2 ≤ 5 := by nlinarith
  have hst : 0 ≤ s*t := mul_nonneg hs.le ht0
  have hst2 : s*t ≤ 2 := by nlinarith
  have hsst : 0 ≤ s^2*t^2 := by positivity
  have hsst4 : s^2*t^2 ≤ 4 := by nlinarith [sq_nonneg (s*t-2)]
  rcases adapted_inverse_coordinates hP.ne' hs.ne' v with ⟨h0,h1,h2⟩
  change P*s^2*ConeGeometry.adapted t v 0 = (y 0 - s*t*y 1 - s^2*t^2*y 2)/(1+t^2) at h0
  change P*s*ConeGeometry.adapted t v 1 = y 1/2 + s*t*y 2 at h1
  change P*ConeGeometry.adapted t v 2 = -(1+t^2)*y 2 at h2
  have hab0 : P*s^2*|ConeGeometry.adapted t v 0| =
      |y 0 - s*t*y 1 - s^2*t^2*y 2|/(1+t^2) := by
    simpa [abs_mul, abs_div, abs_of_nonneg hP.le, abs_of_nonneg (sq_nonneg s),
      abs_of_pos (by positivity : 0 < 1+t^2)] using congrArg abs h0
  have hab1 : P*s*|ConeGeometry.adapted t v 1| = |y 1/2 + s*t*y 2| := by
    simpa [abs_mul, abs_of_nonneg hP.le, abs_of_nonneg hs.le] using congrArg abs h1
  have hab2 : P*|ConeGeometry.adapted t v 2| = (1+t^2)*|y 2| := by
    simpa only [abs_mul, abs_neg, abs_of_nonneg hP.le,
      abs_of_pos (by positivity : 0 < 1+t^2)] using congrArg abs h2
  refine ⟨?_, ?_, ?_⟩
  · rw [hab0]
    have hb : |y 0 - s*t*y 1 - s^2*t^2*y 2| ≤ 7 * ‖y‖ := by
      calc
        _ ≤ |y 0| + |s*t*y 1| + |s^2*t^2*y 2| := (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
        _ = |y 0| + (s*t)*|y 1| + (s^2*t^2)*|y 2| := by
          simp only [abs_mul, abs_of_nonneg hs.le, abs_of_nonneg ht0, abs_of_nonneg (sq_nonneg s), abs_of_nonneg (sq_nonneg t)]
        _ ≤ ‖y‖ + 2*‖y‖ + 4*‖y‖ := by gcongr <;> exact hy _
        _ = _ := by ring
    apply (div_le_iff₀ (by positivity : 0 < 1+t^2)).mpr
    change _ ≤ 9 * ‖y‖ * (1+t^2)
    nlinarith [mul_nonneg hn (sq_nonneg t)]
  · rw [hab1]
    calc
      _ ≤ |y 1/2| + |s*t*y 2| := abs_add_le _ _
      _ = |y 1|/2 + (s*t)*|y 2| := by rw [abs_div, abs_mul, abs_of_nonneg hst]; norm_num
      _ ≤ ‖y‖/2 + 2*‖y‖ := by gcongr <;> exact hy _
      _ ≤ _ := by dsimp [y]; nlinarith [norm_nonneg (dualCoordinates P s t v)]
  · rw [hab2]
    calc
      _ ≤ 5 * ‖y‖ := mul_le_mul ht5 (hy 2) (abs_nonneg _) (by norm_num)
      _ = _ := rfl

end
end CircleDivisor.EnergyV3.AdaptedMetric
