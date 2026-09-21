import CircleDivisor.EnergyV3.ReciprocalConclusion
import CircleDivisor.EnergyV3.ReductionMain

namespace CircleDivisor.EnergyV3

/-- Internal arithmetic and discrepancy reduction from first spacing.
`Main.lean` supplies the analytic premise from `FirstSpacingProof.lean`;
every other premise is a specifically named classical/source input. -/
theorem main_of_firstSpacing
    (hspacing : FirstSpacingStatement) (hLY : LiYangInput)
    (hGK : ElementaryReciprocal.GrahamKolesnikInput)
    (h2 : ClassicalInputs.TwoSquaresIdentity) (hβ : ClassicalInputs.BetaAtOne)
    (hH : ClassicalInputs.HarmonicExpansion) (hV : ClassicalInputs.VaalerApproximation) :
    MainTheoremStatement :=
  main_of_reciprocal_rectangles h2 hβ hH hV
    (ReciprocalConclusion.reciprocalRectangles_of_inputs hspacing hLY hGK)

end CircleDivisor.EnergyV3
