import CircleDivisor.EnergyV3.FirstSpacingProof
import CircleDivisor.EnergyV3.ArithmeticMain

/-! Main result of the September 8 manuscript. All manuscript-specific
steps are proved internally. The assumptions below are precisely the named
external source theorems and five classical formulas, not internal targets. -/

namespace CircleDivisor.EnergyV3

/-- Actual circle and divisor error bounds with exponent `573/1828 + ε`,
conditional only on the explicitly stated external source inputs. -/
theorem main_of_external_inputs
    (hGM : GuthMaldague.GuthMaldagueInput)
    (hLY : LiYangInput)
    (hGK : ElementaryReciprocal.GrahamKolesnikInput)
    (hclassical : ClassicalInputs.Inputs) :
    MainTheoremStatement :=
  main_of_firstSpacing
    (firstSpacing_of_external_inputs hGM hclassical.divisorBound)
    hLY hGK hclassical.twoSquares hclassical.betaAtOne
    hclassical.harmonicExpansion hclassical.vaaler

/-- The same conclusion with the error functions and rational exponent
displayed, to make the final target directly reviewable. -/
theorem circle_and_divisor_error
    (hGM : GuthMaldague.GuthMaldagueInput)
    (hLY : LiYangInput)
    (hGK : ElementaryReciprocal.GrahamKolesnikInput)
    (hclassical : ClassicalInputs.Inputs) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      |circleError X| ≤ C * X ^ ((573 : ℝ) / 1828 + ε) ∧
      |divisorError X| ≤ C * X ^ ((573 : ℝ) / 1828 + ε) :=
  main_of_external_inputs hGM hLY hGK hclassical

end CircleDivisor.EnergyV3
