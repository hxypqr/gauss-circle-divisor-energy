import CircleDivisor.ExternalInterfaces

/-! Strengthened source interface for the revised manuscript. In particular,
the two additional standing inequalities are explicit application premises;
they cannot be inferred merely by pattern-matching the old four-field object.
No result is asserted as an axiom. -/

namespace CircleDivisor.EnergyV3
noncomputable section
open CircleDivisor.ExternalInterfaces

structure StandingConditions (D C H M N R : ℝ) : Prop where
  separation : BlockSeparation D C H M N R
  radius_lower : 2*C*Real.sqrt H+1 ≤ R
  block_radius : H*N^2 ≤ M*R^2

/-- Fixed-q source statement: Li--Yang v2 Lemma 4.4, with its parameter
definitions (4.1), (4.8), (4.12)--(4.14). All six standing scale conditions
are exposed. D≥10 makes `separation.N_small` imply N≤M/10.
The construction constants precede the phase, amplitudes, and all scales.
The V-scale optimization belongs to the proof of this external Lemma 4.4,
not to its application premises; it is not assumed a second time here.
See EXTERNAL_ARITHMETIC_V3_AUDIT.md for this distinction. -/
def LiYangInput : Prop :=
  ∀ q : ℝ, 4 < q → q ≤ 9/2 →
    ∀ c C W ε : ℝ, 0 < c → 2 ≤ C → 1/c ≤ C → 0 < W → 0 < ε →
      ∃ B₀ D M₀ T₀ A : ℝ,
        0 < B₀ ∧ 10 ≤ D ∧ 1 ≤ M₀ ∧ 2 ≤ T₀ ∧ 0 < A ∧
        ∀ F : ℝ → ℝ, PhaseControl c C F →
        ∀ g G : ℝ → ℂ, BVControl W g → BVControl W G →
        ∀ H M T : ℝ, 1 ≤ H → M₀ ≤ M → T₀ ≤ T → M ≤ Real.sqrt T →
        ∀ b : BlockCase, admissibleCase b B₀ H M T →
          ∃ N : ℕ, ∃ R : ℝ,
            0 < N ∧ 0 < R ∧
            Comparable D N (blockLength b H M T) ∧
            Comparable D (R^2) (M^3/(N*T)) ∧
            (StandingConditions D C H M N R →
              ∀ B : ℝ, 0 ≤ B → spacingMajorized D H M N R q B →
                ‖reciprocalSum H M T F g G‖ ≤ A*T^ε*B)

end
end CircleDivisor.EnergyV3
