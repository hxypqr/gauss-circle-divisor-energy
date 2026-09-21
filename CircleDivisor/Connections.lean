import CircleDivisor.ClassicalInputs
import CircleDivisor.SpacingCount
import CircleDivisor.Arithmetic

/-! Explicit connections between independently verified modules and classical inputs. -/

namespace CircleDivisor.Connections
noncomputable section

/-- The exact root satisfies every rational window hypothesis in the arithmetic module. -/
theorem thetaWindow : Arithmetic.ThetaWindow Optimization.theta := by
  have hl := Optimization.theta_lower
  have hu := Optimization.theta_upper
  constructor <;> linarith

/-- Lemma 3.2 with only the external, correctly quantified divisor theorem supplied.
Every internal finite counting step is in `SpacingCount`, rather than an input field.
-/
theorem spacing_count_from_divisor_input (input : ClassicalInputs.DivisorBound)
    (ε : ℝ) (hε : 0 < ε) (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ K L V : ℕ, 1 ≤ K → 1 ≤ L → 1 ≤ V → V ≤ A * K →
      ((SpacingCount.admissibleQuadruples K L V).card : ℝ) ≤
        B * ((K : ℝ) * L) ^ ε * K * (V : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := input ε hε
  have hCone : 1 ≤ C := by simpa using hC 1 (by omega)
  have hdiv : SpacingCount.NaturalDivisorEstimate ε C := by
    intro n hn
    exact hC n (by omega)
  refine ⟨117 * (1 + 2 * C * (2 * (A : ℝ)) ^ ε), by positivity, ?_⟩
  intro K L V hK hL hV hVK
  exact SpacingCount.lemma_3_2 K L V A hK hL hV hA hVK ε C hε.le hCone hdiv

end
end CircleDivisor.Connections
