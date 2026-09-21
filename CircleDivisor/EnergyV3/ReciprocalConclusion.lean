import CircleDivisor.EnergyV3.HardReciprocal
import CircleDivisor.EnergyV3.ElementaryReciprocal
import CircleDivisor.EnergyV3.RectangleWeights

/-! Assemble all parameter regimes into the actual reciprocal rectangle
theorem. The only internal premise is the new first-spacing statement. -/

namespace CircleDivisor.EnergyV3.ReciprocalConclusion
noncomputable section
open CircleDivisor.Arithmetic CircleDivisor.ExternalInterfaces
open CircleDivisor.LogScale ElementaryReciprocal HardReciprocal

theorem weighted_reciprocal_of_inputs (hspacing : FirstSpacingStatement) (hLY : LiYangInput)
    (hGK : GrahamKolesnikInput) (W ε : ℝ) (hW : 0 < W) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ T H M a σ b : ℝ,
      2 ≤ T → 1 ≤ H → 1 ≤ M → M ≤ Real.sqrt T → H ≤ M*T^(-theta) →
      1/4 ≤ a → a ≤ 1 → 0 ≤ σ → σ ≤ 1 →
      ∀ g G : ℝ → ℂ, BVControl W g → BVControl W G →
        ‖reciprocalSum H M T (ReciprocalPhase.phase a σ b) g G‖ ≤ A*H*T^(theta+ε) := by
  obtain ⟨T₀,A₀,hT₀,hA₀,hhard⟩ := hard_reciprocal_uniform hspacing hLY
    (1/10000) 10000 W ε (by norm_num) (by norm_num) (by norm_num) hW hε
  obtain ⟨C,hC,heasy⟩ := elementary_double_sum hGK W hW
  let A := A₀+2*C+4*W^2*T₀
  have hA : 0 < A := by dsimp [A]; positivity
  have hCT : 0 ≤ 4*W^2*T₀ := by positivity
  have hCA : 2*C ≤ A := by dsimp [A]; linarith
  have hA₀A : A₀ ≤ A := by dsimp [A]; linarith
  have hTA : 4*W^2*T₀ ≤ A := by dsimp [A]; linarith
  refine ⟨A,hA,?_⟩
  intro T H M a σ b hT hH hM hMT hHM ha ha' hσ hσ' g G hg hG
  have ht : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hHp : 0 < H := by linarith
  have hMp : 0 < M := by linarith
  have hθ : 0 < theta := by norm_num [theta]
  have hone : 1 ≤ T^(theta+ε) := Real.one_le_rpow hT1.le (by linarith)
  have hθe : T^theta ≤ T^(theta+ε) := Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith)
  have hmono : ∀ A' : ℝ, A' ≤ A → A'*H*T^(theta+ε) ≤ A*H*T^(theta+ε) := by
    intro A' hA'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA' hHp.le) (by positivity)
  by_cases hlarge : T₀ ≤ T
  · let h := exponent T H
    let m := exponent T M
    have hrep : T^h=H := rpow_exponent T H hT1 hHp
    have mrep : T^m=M := rpow_exponent T M hT1 hMp
    have hupper : h ≤ m-theta := by
      apply (Real.rpow_le_rpow_left_iff hT1).mp
      rw [Real.rpow_sub ht, hrep, mrep, div_eq_mul_inv, ← Real.rpow_neg ht.le]
      exact hHM
    have mupper : m ≤ 1/2 := by
      apply (Real.rpow_le_rpow_left_iff hT1).mp
      rw [mrep]
      rw [Real.sqrt_eq_rpow] at hMT
      exact hMT
    rcases easy_or_hard theta h m hupper mupper with hpair | hsecond | hr
    · have hx : (H*T)^((2:ℝ)/7) ≤ T^theta := by
        have hid : H*T = T^(h+1) := by rw [Real.rpow_add ht, Real.rpow_one, hrep]
        rw [hid, ← Real.rpow_mul ht.le]
        exact Real.rpow_le_rpow_of_exponent_le hT1.le hpair
      have hb := (heasy T H M a σ b hT hH hM hMT ha ha' hσ hσ' g G hg hG).1
      calc
        _ ≤ C*H*((H*T)^((2:ℝ)/7)+1) := hb
        _ ≤ C*H*(2*T^(theta+ε)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (2*C)*H*T^(theta+ε) := by ring
        _ ≤ _ := hmono (2*C) hCA
    · have hx : (H*T/M)^((1:ℝ)/2) ≤ T^theta := by
        have hid : H*T/M = T^(h+1-m) := by
          rw [Real.rpow_sub ht, Real.rpow_add ht, Real.rpow_one, hrep, mrep]
        rw [hid, ← Real.rpow_mul ht.le]
        exact Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith)
      have hquarter : T^((1:ℝ)/4) ≤ T^(theta+ε) :=
        Real.rpow_le_rpow_of_exponent_le hT1.le (by norm_num [theta]; linarith)
      have hb := (heasy T H M a σ b hT hH hM hMT ha ha' hσ hσ' g G hg hG).2
      calc
        _ ≤ C*H*((H*T/M)^((1:ℝ)/2)+T^((1:ℝ)/4)) := hb
        _ ≤ C*H*(2*T^(theta+ε)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (2*C)*H*T^(theta+ε) := by ring
        _ ≤ _ := hmono (2*C) hCA
    · have hphase := ReciprocalPhase.reciprocal_phase_control a σ b
        (by rwa [abs_of_pos (by linarith : 0<a)])
        (by rwa [abs_of_pos (by linarith : 0<a)]) hσ hσ'
      have hb := hhard T hlarge h m hr (ReciprocalPhase.phase a σ b) hphase g G hg hG
      rw [hrep,mrep] at hb
      exact hb.trans (hmono A₀ hA₀A)
  · have hMT₀ : M ≤ T₀ := by
      have hs : Real.sqrt T ≤ T := (Real.sqrt_le_iff).mpr ⟨ht.le, by nlinarith⟩
      linarith
    have hb := reciprocalSum_trivial (T := T) hH hM hW.le (ReciprocalPhase.phase a σ b) g G hg hG
    calc
      _ ≤ 4*W^2*H*M := hb
      _ ≤ 4*W^2*H*T₀ := mul_le_mul_of_nonneg_left hMT₀ (by positivity)
      _ ≤ (4*W^2*T₀)*H*T^(theta+ε) := by
        have he := mul_le_mul_of_nonneg_left hone (show 0 ≤ 4*W^2*H*T₀ by positivity)
        nlinarith
      _ ≤ _ := hmono (4*W^2*T₀) hTA

theorem reciprocalRectangles_of_inputs (hspacing : FirstSpacingStatement) (hLY : LiYangInput)
    (hGK : GrahamKolesnikInput) : ReciprocalRectangles theta := by
  intro ε hε
  obtain ⟨A,hA,hbound⟩ := weighted_reciprocal_of_inputs hspacing hLY hGK 1 ε (by norm_num) hε
  refine ⟨A,hA,?_⟩
  intro T hT M hM hMT a σ b ha ha' hσ hσ' V hMV hVM H hH hHM n hn
  rw [← reciprocalSum_upperCutoffs H M n V hH hM hn hMV hVM T
    (ReciprocalPhase.phase a σ b)]
  apply hbound T H M a σ b hT (by exact_mod_cast hH) (by exact_mod_cast hM) hMT
    _ ha ha' hσ hσ' _ _ (upperCutoff_BV _) (upperCutoff_BV _)
  simpa only [div_eq_mul_inv, Real.rpow_neg (show 0≤T by linarith)] using hHM

end
end CircleDivisor.EnergyV3.ReciprocalConclusion
