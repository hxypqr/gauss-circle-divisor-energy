import CircleDivisor.EnergyV3.ReductionReciprocal
import CircleDivisor.EnergyV3.Statements
import CircleDivisor.DiscrepancyReduction

/-! Exact character residue-class assembly, followed by the previously proved
hyperbola reductions. This closes §7 conditional only on the internal §6
reciprocal rectangle theorem and the stated classical external inputs. -/

namespace CircleDivisor.EnergyV3
noncomputable section
open scoped BigOperators

theorem character_four_blocks (f : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.range (4 * N), (Sawtooth.chi4 d : ℝ) * f d) =
      ∑ j ∈ Finset.range N, (f (4 * j + 1) - f (4 * j + 3)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 4 * (N + 1) = 4 * N + 4 by omega, Finset.sum_range_add, ih,
      Finset.sum_range_succ]
    congr 1
    norm_num [Finset.sum_range_succ, Sawtooth.chi4, Nat.add_mod, Nat.mul_mod]
    ring

theorem sum_range_split_first (f : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, f j) = f 0 + ∑ j ∈ Finset.Icc 1 (N - 1), f j := by
  rw [← Finset.sum_range_add_sum_Ico f hN]
  simp only [Finset.sum_range_one]
  congr 1

theorem character_sawtooth_bound (X B : ℝ) (U : ℕ) (hB : 0 ≤ B)
    (hrecip : ∀ r : ℝ, 1 ≤ r → r ≤ 3 → ∀ N : ℕ, N ≤ U →
      |∑ j ∈ Finset.Icc 1 N, Sawtooth.psi (X * (1 / 4) / (j + r / 4))| ≤ B) :
    |∑ d ∈ Finset.Icc 1 U, (Sawtooth.chi4 d : ℝ) * Sawtooth.psi (X / d)| ≤
      2 * B + 3 := by
  let N := (U + 1) / 4
  let R := (U + 1) % 4
  let f : ℕ → ℝ := fun d => (Sawtooth.chi4 d : ℝ) * Sawtooth.psi (X / d)
  have hsplit : (∑ d ∈ Finset.range (U + 1), f d) =
      (∑ d ∈ Finset.range (4 * N), f d) +
      ∑ j ∈ Finset.range R, f (4 * N + j) := by
    have hUR : U + 1 = 4 * N + R := by
      dsimp [N, R]
      omega
    conv_lhs => rw [hUR]
    exact Finset.sum_range_add _ _ _
  have hf (d : ℕ) : |f d| ≤ 1 / 2 := by
    have hchi : |(Sawtooth.chi4 d : ℝ)| ≤ 1 := by exact_mod_cast Sawtooth.chi4_abs_le d
    dsimp [f]
    rw [abs_mul]
    have hh := mul_le_mul hchi (Sawtooth.abs_psi_le (X / d))
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  have htail : |∑ j ∈ Finset.range R, f (4 * N + j)| ≤ 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range R, (1 / 2 : ℝ) := Finset.sum_le_sum (fun j hj => hf _)
      _ ≤ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hR : R < 4 := Nat.mod_lt _ (by omega)
        have hR' : (R : ℝ) ≤ 3 := by exact_mod_cast (by omega : R ≤ 3)
        linarith
  have hprogression (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) :
      |∑ j ∈ Finset.range N, Sawtooth.psi (X / (4 * j + r : ℕ))| ≤ B + 1 / 2 := by
    by_cases hN0 : N = 0
    · simp [hN0]
      linarith
    have hN : 1 ≤ N := by omega
    rw [sum_range_split_first _ N hN]
    have hNU : N - 1 ≤ U := by dsimp [N]; omega
    have hh := hrecip r (by exact_mod_cast hr) (by exact_mod_cast hr') (N - 1) hNU
    have heq : (∑ j ∈ Finset.Icc 1 (N - 1), Sawtooth.psi (X / (4 * j + r : ℕ))) =
        ∑ j ∈ Finset.Icc 1 (N - 1), Sawtooth.psi (X * (1 / 4) / (j + (r : ℝ) / 4)) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      push_cast
      field_simp
      <;> ring
    rw [heq]
    exact (abs_add_le _ _).trans (by
      have hh0 := Sawtooth.abs_psi_le (X / (4 * 0 + r : ℕ))
      linarith)
  have hblocks : |∑ d ∈ Finset.range (4 * N), f d| ≤ 2 * B + 1 := by
    rw [show (∑ d ∈ Finset.range (4 * N), f d) =
        ∑ j ∈ Finset.range N,
          (Sawtooth.psi (X / (4 * j + 1 : ℕ)) - Sawtooth.psi (X / (4 * j + 3 : ℕ)))
      from character_four_blocks (fun d => Sawtooth.psi (X / d)) N]
    rw [Finset.sum_sub_distrib]
    have h1 := hprogression 1 (by omega) (by omega)
    have h3 := hprogression 3 (by omega) (by omega)
    exact (abs_sub _ _).trans (by linarith)
  have htarget : (∑ d ∈ Finset.Icc 1 U, (Sawtooth.chi4 d : ℝ) * Sawtooth.psi (X / d)) =
      ∑ d ∈ Finset.range (U + 1), f d := by
    have hh := sum_range_split_first f (U + 1) (by omega)
    simpa [f, Sawtooth.chi4] using hh.symm
  rw [htarget, hsplit]
  exact (abs_add_le _ _).trans (by linarith)

theorem main_of_fullReciprocalSawtooth
    (h2 : ClassicalInputs.TwoSquaresIdentity) (hβ : ClassicalInputs.BetaAtOne)
    (hH : ClassicalInputs.HarmonicExpansion) (hs : FullReciprocalSawtooth theta) :
    MainTheoremStatement := by
  obtain ⟨B, hB, hdiv⟩ := DiscrepancyReduction.divisorError_sawtooth hH
  intro ε hε
  obtain ⟨C, hC, hsaw⟩ := hs ε hε
  refine ⟨35 + B + 16 * C, by positivity, ?_⟩
  intro X hX
  let U := ⌊Real.sqrt X⌋₊
  have hU : (U : ℝ) ≤ Real.sqrt X := Nat.floor_le (Real.sqrt_nonneg X)
  have hX0 : 0 < X := by linarith
  have htheta : 0 < theta := by norm_num [theta]
  have hp : 1 ≤ X ^ (theta + ε) := Real.one_le_rpow (by linarith) (by linarith)
  have hfull (a σ b : ℝ) (ha : 1 / 4 ≤ a) (ha' : a ≤ 1) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
      (N : ℕ) (hN : N ≤ U) :
      |∑ m ∈ Finset.Icc 1 N, Sawtooth.psi (X * a / (m + σ) + b)| ≤
        C * X ^ (theta + ε) :=
    hsaw X hX N ((by exact_mod_cast hN : (N : ℝ) ≤ U).trans hU) a σ b ha ha' hσ hσ'
  have hchi := character_sawtooth_bound X (C * X ^ (theta + ε)) U (by positivity)
    (by
      intro r hr hr' N hN
      simpa using hfull (1 / 4) (r / 4) 0 (by norm_num) (by norm_num)
        (by positivity) (by linarith) N hN)
  have hd : |∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / m)| ≤ C * X ^ (theta + ε) := by
    simpa using hfull 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) U le_rfl
  have hshift (b : ℝ) :
      |∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / (4 * m) + b)| ≤ C * X ^ (theta + ε) := by
    have hh := hfull (1 / 4) 0 b (by norm_num) (by norm_num) (by norm_num) (by norm_num) U le_rfl
    convert hh using 1
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    ring
  have hcircle : |DiscrepancyReduction.circleSawtooth X U| ≤ 16 * C * X ^ (theta + ε) + 12 := by
    unfold DiscrepancyReduction.circleSawtooth
    rw [Finset.sum_sub_distrib]
    have hs1 := hshift (1 / 4)
    have hs3 := hshift (3 / 4)
    have hsub := abs_sub
      (∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / (4 * m) + 1 / 4))
      (∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / (4 * m) + 3 / 4))
    have htri := abs_add_le
      (-4 * ∑ d ∈ Finset.Icc 1 U, (Sawtooth.chi4 d : ℝ) * Sawtooth.psi (X / d))
      (4 * ((∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / (4 * m) + 1 / 4)) -
        ∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / (4 * m) + 3 / 4)))
    simp only [abs_mul, abs_neg] at htri
    norm_num at htri
    simp only [neg_mul]
    linarith
  constructor
  · have he := DiscrepancyReduction.circleError_sawtooth h2 hβ X (by linarith)
    have ht := abs_add_le (circleError X - DiscrepancyReduction.circleSawtooth X U)
      (DiscrepancyReduction.circleSawtooth X U)
    rw [sub_add_cancel] at ht
    change |circleError X - DiscrepancyReduction.circleSawtooth X U| ≤ 23 at he
    nlinarith
  · have he := hdiv X (by linarith)
    have ht := abs_sub (divisorError X + 2 * ∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / m))
      (2 * ∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / m))
    rw [add_sub_cancel_right, abs_mul] at ht
    norm_num at ht
    change |divisorError X + 2 * ∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (X / m)| ≤ B at he
    nlinarith

/-- Every internal inference of §7, composed with the exact classical reductions.
`hrect` is the still separate internal §6 target, rather than an external axiom. -/
theorem main_of_reciprocal_rectangles
    (h2 : ClassicalInputs.TwoSquaresIdentity) (hβ : ClassicalInputs.BetaAtOne)
    (hH : ClassicalInputs.HarmonicExpansion) (hV : ClassicalInputs.VaalerApproximation)
    (hrect : ReciprocalRectangles theta) : MainTheoremStatement := by
  apply main_of_fullReciprocalSawtooth h2 hβ hH
  apply fullReciprocalSawtooth_of_dyadic
  exact dyadicReciprocalSawtooth_of_rectangles theta (by norm_num [theta]) hV hrect

end
end CircleDivisor.EnergyV3
