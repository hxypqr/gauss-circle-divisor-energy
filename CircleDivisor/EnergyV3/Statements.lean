import CircleDivisor.EnergyV3.Arithmetic
import CircleDivisor.Statements

/-! Statements for the September 8 manuscript. These reuse the actual lattice
count, divisor sum and exponential sums, but use the revised exponent and the
revised third monomial. Definitions of propositions are not proofs. -/

namespace CircleDivisor.EnergyV3
noncomputable section

def MainTheoremStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
    |circleError X| ≤ C * X ^ (theta + ε) ∧
    |divisorError X| ≤ C * X ^ (theta + ε)

def FirstSpacingStatement : Prop :=
  ∀ q : ℝ, 4 < q → q ≤ 9 / 2 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ K L : ℝ, 1 ≤ L → L ≤ K →
      ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
        coneMoment K L q a ≤ C * (K * L) ^ ε * Arithmetic.fourTerm K L q

/-- The manuscript's uniform first-spacing assertion: the constant depends on
`ε`, while the entire endpoint loss in `q` is displayed explicitly. -/
def UniformFirstSpacingStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℝ, 4 < q → q ≤ 9 / 2 → ∀ K L : ℝ, 1 ≤ L → L ≤ K →
      ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
        coneMoment K L q a ≤ C * (q / (q - 4)) * (K * L) ^ ε * Arithmetic.fourTerm K L q

theorem firstSpacing_of_uniform (h : UniformFirstSpacingStatement) : FirstSpacingStatement := by
  intro q hq hqu ε hε
  obtain ⟨C,hC,hb⟩ := h ε hε
  refine ⟨C * (q / (q - 4)), mul_pos hC (div_pos (by linarith) (by linarith)), ?_⟩
  exact hb q hq hqu

end
end CircleDivisor.EnergyV3
