import CircleDivisor.Optimization
import CircleDivisor.Sawtooth

/-!
# Actual objects and target statements

The definitions in this file are specifications, not proofs of the manuscript's
Theorems 1.1 and 1.2. A `Prop` definition has no proof merely because it compiles.
-/

namespace CircleDivisor
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- All lattice points, without a coordinate truncation or a surrogate sequence. -/
def circleCount (X : ℝ) : ℕ :=
  {p : ℤ × ℤ | (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ X}.ncard

def circleError (X : ℝ) : ℝ := circleCount X - Real.pi * X

def divisorSummatory (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n.divisors.card : ℝ)

def divisorError (X : ℝ) : ℝ :=
  divisorSummatory X - X * Real.log X - (2 * Real.eulerMascheroniConstant - 1) * X

/-- Theorem 1.1 in the squared-radius variable, including both discrepancies. -/
def MainTheoremStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
    |circleError X| ≤ C * X ^ (Optimization.theta + ε) ∧
    |divisorError X| ≤ C * X ^ (Optimization.theta + ε)

def exponential (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)

def dyadicIntegers (K : ℝ) : Finset ℤ := Finset.Ico ⌈K⌉ ⌈2 * K⌉

def coneSum (K L : ℝ) (a : ℤ → ℤ → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  ∑ k ∈ dyadicIntegers K, ∑ l ∈ dyadicIntegers L,
    a k l * exponential ((l : ℝ) * x 0 + (k : ℝ) * l * x 1 + l * Real.sqrt k * x 2)

def momentBox (K : ℝ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => if i = 2 then Set.Icc (-Real.sqrt K) (Real.sqrt K) else Set.Icc 0 1)

/-- The normalized moment for an actual coefficient array, before taking its supremum. -/
def coneMoment (K L q : ℝ) (a : ℤ → ℤ → ℂ) : ℝ :=
  (2 * Real.sqrt K)⁻¹ * ∫ x in momentBox K, ‖coneSum K L a x‖ ^ q

def fourTermBound (K L q : ℝ) : ℝ :=
  (K * L) ^ (q / 2) + K * L ^ (2 * q - 5) +
    K ^ (q - 2) * L ^ ((q - 1) / 2) + K ^ (3 * q / 4 - 2) * L ^ (5 * q / 4 - 2)

/-- Theorem 1.2, uniformly in the actual bounded coefficient arrays. -/
def FirstSpacingStatement : Prop :=
  ∀ q : ℝ, 4 < q → q ≤ 9 / 2 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ K L : ℝ, 1 ≤ L → L ≤ K →
      ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
        coneMoment K L q a ≤ C * (K * L) ^ ε * fourTermBound K L q

/-- The compact-uniform version needed when q=q(x) varies in Section 6.
`UniformMoment.lean` proves its equivalence to the preceding statement using
the actual finite sum, a finite q grid, and an arbitrarily small power loss. -/
def FirstSpacingUniformStatement : Prop :=
  ∀ q₀ : ℝ, 4 < q₀ → q₀ ≤ 9 / 2 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, q₀ ≤ q → q ≤ 9 / 2 →
      ∀ K L : ℝ, 1 ≤ L → L ≤ K →
        ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
          coneMoment K L q a ≤ C * (K * L) ^ ε * fourTermBound K L q

theorem firstSpacing_of_uniform (h : FirstSpacingUniformStatement) : FirstSpacingStatement := by
  intro q hq hq' ε hε
  obtain ⟨C, hC, hbound⟩ := h q hq hq' ε hε
  exact ⟨C, hC, hbound q le_rfl hq'⟩

def reciprocalSum (H M T : ℝ) (F : ℝ → ℝ) (g G : ℝ → ℂ) : ℂ :=
  ∑ h ∈ dyadicIntegers H, ∑ m ∈ dyadicIntegers M,
    g (h / H) * G (m / M) * exponential ((h * T / M) * F (m / M))

end
end CircleDivisor
