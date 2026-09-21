import CircleDivisor.DiscrepancyReduction

/-! The final bounded-error absorption, expressed as a CONDITIONAL theorem.
`SawtoothBounds` is an internal, still unproved obligation, not a literature
input. No declaration here proves MainTheoremStatement unconditionally. -/

namespace CircleDivisor.FinalAssembly
noncomputable section
open DiscrepancyReduction
open scoped BigOperators

/-- The exact remaining sawtooth bounds after the two proved hyperbola reductions.
These must be derived internally from the analytic input and the reciprocal sums. -/
def SawtoothBounds : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
    |circleSawtooth X ⌊Real.sqrt X⌋₊| ≤ C * X ^ (Optimization.theta + ε) ∧
    |∑ a ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊, Sawtooth.psi (X / a)| ≤
      C * X ^ (Optimization.theta + ε)

theorem main_of_sawtooth_bounds
    (h2 : ClassicalInputs.TwoSquaresIdentity) (hβ : ClassicalInputs.BetaAtOne)
    (hH : ClassicalInputs.HarmonicExpansion) (hs : SawtoothBounds) :
    MainTheoremStatement := by
  obtain ⟨B, hB, hdiv⟩ := divisorError_sawtooth hH
  intro ε hε
  obtain ⟨C, hC, hb⟩ := hs ε hε
  refine ⟨23 + B + 2 * C, by positivity, ?_⟩
  intro X hX
  obtain ⟨hcirc, hsaw⟩ := hb X hX
  have hp : 1 ≤ X ^ (Optimization.theta + ε) := by
    apply Real.one_le_rpow (by linarith)
    have ht := Optimization.theta_lower
    linarith
  constructor
  · have htriangle := abs_add_le
      (circleError X - circleSawtooth X ⌊Real.sqrt X⌋₊)
      (circleSawtooth X ⌊Real.sqrt X⌋₊)
    rw [sub_add_cancel] at htriangle
    have herror := circleError_sawtooth h2 hβ X (by linarith)
    nlinarith
  · let S := ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊, Sawtooth.psi (X / a)
    have htriangle := abs_sub (divisorError X + 2 * S) (2 * S)
    rw [add_sub_cancel_right, abs_mul] at htriangle
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htriangle
    have herror := hdiv X (by linarith)
    change |divisorError X + 2 * S| ≤ B at herror
    change |S| ≤ C * X ^ (Optimization.theta + ε) at hsaw
    nlinarith

end
end CircleDivisor.FinalAssembly
