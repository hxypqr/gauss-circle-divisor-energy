import CircleDivisor.EnergyV3.ReductionPower
import CircleDivisor.ReciprocalPhase

namespace CircleDivisor.EnergyV3
noncomputable section
open scoped BigOperators

/-- A sufficient specialization of the internal §6 rectangle theorem. The
position interval is genuine, may be truncated, and all constants are uniform
in the additive phase. This is not an external input. -/
def ReciprocalRectangles (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Real.sqrt T →
    ∀ a σ b : ℝ, 1 / 4 ≤ a → a ≤ 1 → 0 ≤ σ → σ ≤ 1 →
    ∀ V : ℕ, M ≤ V → V ≤ 2 * M →
    ∀ H : ℕ, 1 ≤ H → (H : ℝ) ≤ M / T ^ θ → ∀ n : ℕ, n ≤ H →
      ‖∑ i ∈ Finset.range n, frequencySum (Finset.Ico M V)
        (fun m : ℕ => (T / M) * ReciprocalPhase.phase a σ b ((m : ℝ) / M))
        (H + i)‖ ≤ C * H * T ^ (θ + ε)

def DyadicReciprocalSawtooth (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Real.sqrt T →
    ∀ a σ b : ℝ, 1 / 4 ≤ a → a ≤ 1 → 0 ≤ σ → σ ≤ 1 →
    ∀ V : ℕ, M ≤ V → V ≤ 2 * M →
      |∑ m ∈ Finset.Ico M V,
        Sawtooth.psi ((T / M) * ReciprocalPhase.phase a σ b ((m : ℝ) / M))| ≤
          C * T ^ (θ + ε)

theorem dyadicReciprocalSawtooth_of_rectangles (θ : ℝ) (hθ : 0 ≤ θ)
    (hV : ClassicalInputs.VaalerApproximation) (hrect : ReciprocalRectangles θ) :
    DyadicReciprocalSawtooth θ := by
  intro ε hε
  obtain ⟨C, hC, hrectC⟩ := hrect (ε / 2) (by linarith)
  obtain ⟨D, hD, hsaw⟩ := rectangle_to_sawtooth_power hV θ ε C hθ hε hC
  refine ⟨D, hD, ?_⟩
  intro T hT M hM hMT a σ b ha ha' hσ hσ' V hMV hVM
  apply hsaw (Finset.Ico M V)
    (fun m : ℕ => (T / M) * ReciprocalPhase.phase a σ b ((m : ℝ) / M))
    T M hT (by positivity)
  · apply hMT.trans
    exact (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩
  · simp only [Nat.card_Ico]
    exact_mod_cast (by omega : V - M ≤ 2 * M)
  · exact hrectC T hT M hM hMT a σ b ha ha' hσ hσ' V hMV hVM

def FullReciprocalSawtooth (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ U : ℕ, (U : ℝ) ≤ Real.sqrt T →
    ∀ a σ b : ℝ, 1 / 4 ≤ a → a ≤ 1 → 0 ≤ σ → σ ≤ 1 →
      |∑ m ∈ Finset.Icc 1 U, Sawtooth.psi (T * a / (m + σ) + b)| ≤
        C * T ^ (θ + ε)

theorem fullReciprocalSawtooth_of_dyadic (θ : ℝ)
    (hsaw : DyadicReciprocalSawtooth θ) : FullReciprocalSawtooth θ := by
  intro ε hε
  obtain ⟨C, hC, hlocal⟩ := hsaw (ε / 2) (by linarith)
  let L := 1 / ((ε / 2) * Real.log 2) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C * L, mul_pos hC hL, ?_⟩
  intro T hT U hUT a σ b ha ha' hσ hσ'
  by_cases hU0 : U = 0
  · subst U
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty, abs_zero]
    positivity
  have hU : 1 ≤ U := by omega
  have hblocks : ∀ j ≤ Nat.log 2 U,
      ‖∑ m ∈ dyadicBlock U j, Sawtooth.psi (T * a / (m + σ) + b)‖ ≤
        C * T ^ (θ + ε / 2) := by
    intro j hj
    let M : ℕ := 2 ^ j
    let V := min (2 ^ (j + 1)) (U + 1)
    have hM : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
    have hMU : M ≤ U := dyadic_block_start_le U j hU hj
    have hMT : (M : ℝ) ≤ Real.sqrt T := (by exact_mod_cast hMU : (M : ℝ) ≤ U).trans hUT
    have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
    have hMV : M ≤ V := by
      dsimp [V]
      rw [pow_succ]
      omega
    have hVM : V ≤ 2 * M := by
      dsimp [V, M]
      rw [pow_succ]
      omega
    have hσM : σ / M ≤ 1 := by
      rw [div_le_one hMr]
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hh := hlocal T hT M hM hMT a (σ / M) (M * b / T)
      ha ha' (by positivity) hσM V hMV hVM
    have heq : ∀ m ∈ Finset.Ico M V,
        (T / M) * ReciprocalPhase.phase a (σ / M) (M * b / T) ((m : ℝ) / M) =
          T * a / (m + σ) + b := by
      intro m hm
      have hmM := (Finset.mem_Ico.mp hm).1
      have hmpos : 0 < (m : ℝ) + σ := by
        have : (M : ℝ) ≤ m := by exact_mod_cast hmM
        linarith
      have hTne : T ≠ 0 := by linarith
      unfold ReciprocalPhase.phase
      field_simp
      <;> ring
    have heqsum := Finset.sum_congr rfl (fun m hm => congrArg Sawtooth.psi (heq m hm))
    rw [heqsum] at hh
    exact hh
  have hh := norm_sum_le_dyadic_constant
    (fun m : ℕ => Sawtooth.psi (T * a / (m + σ) + b)) U
    (C * T ^ (θ + ε / 2)) hblocks
  rw [Real.norm_eq_abs] at hh
  have hUT' : (U : ℝ) ≤ T := hUT.trans
    ((Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩)
  have hcount := dyadic_count_le_power U hU T (ε / 2) (by linarith) hUT' (by linarith)
  have hprod := mul_le_mul_of_nonneg_right hcount
    (by positivity : 0 ≤ C * T ^ (θ + ε / 2))
  have hpow : T ^ (θ + ε / 2) * T ^ (ε / 2) = T ^ (θ + ε) := by
    rw [← Real.rpow_add (by linarith : 0 < T)]
    congr 1
    ring
  calc
    _ ≤ (Nat.log 2 U + 1) * (C * T ^ (θ + ε / 2)) := hh
    _ ≤ (L * T ^ (ε / 2)) * (C * T ^ (θ + ε / 2)) := hprod
    _ = C * L * (T ^ (θ + ε / 2) * T ^ (ε / 2)) := by ring
    _ = _ := by rw [hpow]

end
end CircleDivisor.EnergyV3
