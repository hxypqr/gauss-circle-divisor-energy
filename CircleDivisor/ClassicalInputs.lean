import CircleDivisor.Statements

/-!
# Precisely stated classical input propositions

These are named hypotheses, not new axioms, and no proofs of them are claimed.
They are only the classical inputs below, not a completed formalization of the
Guth–Maldague or Li–Yang interfaces. See DEPENDENCIES.md for that distinction.
-/

namespace CircleDivisor.ClassicalInputs
noncomputable section
open Filter
open scoped Topology BigOperators

def twoSquaresCount (n : ℕ) : ℕ :=
  {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)}.ncard

/-- The classical two-squares coefficient formula, for positive n only. -/
def TwoSquaresIdentity : Prop :=
  ∀ n : ℕ, 1 ≤ n → (twoSquaresCount n : ℤ) = 4 * ∑ d ∈ n.divisors, Sawtooth.chi4 d

/-- Ordered partial sums, since the beta series is conditionally convergent. -/
def BetaAtOne : Prop :=
  Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, (Sawtooth.chi4 d : ℝ) / d)
    atTop (𝓝 (Real.pi / 4))

/-- The precise error order needed for the O(1) divisor cancellation. -/
def HarmonicExpansion : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant - 1 / (2 * n)| ≤
      C / (n : ℝ) ^ 2

/-- A standard divisor estimate; its epsilon and constant precede the integer. -/
def DivisorBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

def vaalerWeight (u : ℝ) : ℝ :=
  if u = 0 then 1 else if u = 1 then 0 else
    Real.pi * u * (1 - u) * (Real.cos (Real.pi * u) / Real.sin (Real.pi * u)) + u

def vaalerApproximation (Y : ℕ) (t : ℝ) : ℝ :=
  -(∑ h ∈ Finset.Icc 1 Y,
    vaalerWeight ((h : ℝ) / (Y + 1)) * Real.sin (2 * Real.pi * h * t) / (Real.pi * h))

def fejerRemainder (Y : ℕ) (t : ℝ) : ℝ :=
  (1 / 2 + ∑ h ∈ Finset.Icc 1 Y,
    (1 - (h : ℝ) / (Y + 1)) * Real.cos (2 * Real.pi * h * t)) / (Y + 1)

/-- Vaaler's finite approximation, including the manuscript's value at integers. -/
def VaalerApproximation : Prop :=
  ∀ Y : ℕ, 1 ≤ Y → ∀ t : ℝ,
    |Sawtooth.psi t - vaalerApproximation Y t| ≤ fejerRemainder Y t

structure Inputs : Prop where
  twoSquares : TwoSquaresIdentity
  betaAtOne : BetaAtOne
  harmonicExpansion : HarmonicExpansion
  divisorBound : DivisorBound
  vaaler : VaalerApproximation

theorem two_squares (inputs : Inputs) (n : ℕ) (hn : 1 ≤ n) :
    (twoSquaresCount n : ℤ) = 4 * ∑ d ∈ n.divisors, Sawtooth.chi4 d :=
  inputs.twoSquares n hn

theorem beta_ordered_limit (inputs : Inputs) : BetaAtOne := inputs.betaAtOne

theorem harmonic_remainder (inputs : Inputs) : HarmonicExpansion := inputs.harmonicExpansion

theorem divisor_bound (inputs : Inputs) : DivisorBound := inputs.divisorBound

theorem vaaler_error (inputs : Inputs) (Y : ℕ) (hY : 1 ≤ Y) (t : ℝ) :
    |Sawtooth.psi t - vaalerApproximation Y t| ≤ fejerRemainder Y t := inputs.vaaler Y hY t

end
end CircleDivisor.ClassicalInputs
