import CircleDivisor.EnergyV3.Optimization
import CircleDivisor.ReciprocalPhase
import CircleDivisor.UniformMoment

/-! The classical one-dimensional Graham--Kolesnik input, specialized to the
compact reciprocal phase family, and its internal summation over frequencies.
The input is a proposition, never an axiom. It is the exponent-pair (2/7,4/7)
and second-derivative bounds of Chapters 2--3 / Theorem 2.2, with partial
summation for a BV amplitude. The phase's additive constant is unrestricted.
The displayed forms use M≤sqrt T and y≥1 to bound the elementary remainder.
No two-dimensional or target-exponent estimate is included in the input. -/

namespace CircleDivisor.EnergyV3.ElementaryReciprocal
noncomputable section
open CircleDivisor.ExternalInterfaces
open scoped BigOperators

def innerSum (M T y a σ b : ℝ) (G : ℝ → ℂ) : ℂ :=
  ∑ m ∈ dyadicIntegers M, G (m/M) *
    exponential ((y*T/M) * ReciprocalPhase.phase a σ b (m/M))

def GrahamKolesnikInput : Prop :=
  ∀ W : ℝ, 0 < W → ∃ C : ℝ, 0 < C ∧
    ∀ T M y a σ b : ℝ, 2 ≤ T → 1 ≤ M → M ≤ Real.sqrt T → 1 ≤ y →
    1/4 ≤ a → a ≤ 1 → 0 ≤ σ → σ ≤ 1 →
    ∀ G : ℝ → ℂ, BVControl W G →
      ‖innerSum M T y a σ b G‖ ≤ C*((y*T)^((2:ℝ)/7)+1) ∧
      ‖innerSum M T y a σ b G‖ ≤ C*((y*T/M)^((1:ℝ)/2)+T^((1:ℝ)/4))

theorem dyadic_mem_bounds {H : ℝ} {h : ℤ} (hh : h ∈ dyadicIntegers H) :
    H ≤ (h:ℝ) ∧ (h:ℝ) < 2*H := by
  rcases Finset.mem_Ico.mp hh with ⟨hl,hu⟩
  exact ⟨(Int.ceil_le).mp hl, (Int.lt_ceil).mp hu⟩

theorem dyadic_ratio_bounds {H : ℝ} {h : ℤ} (hH : 0 < H)
    (hh : h ∈ dyadicIntegers H) : (h:ℝ)/H ∈ Set.Icc (1:ℝ) 2 := by
  have hb := dyadic_mem_bounds hh
  constructor
  · exact (le_div_iff₀ hH).mpr (by linarith [hb.1])
  · exact (div_le_iff₀ hH).mpr (by linarith [hb.2])

theorem norm_reciprocalSum_le {H M T B W : ℝ} (hH : 1 ≤ H) (hW : 0 ≤ W)
    (hB : 0 ≤ B) (F : ℝ → ℝ) (g G : ℝ → ℂ) (hg : BVControl W g)
    (hinner : ∀ h ∈ dyadicIntegers H,
      ‖∑ m ∈ dyadicIntegers M, G (m/M)*exponential ((h*T/M)*F (m/M))‖ ≤ B) :
    ‖reciprocalSum H M T F g G‖ ≤ 2*H*W*B := by
  have hHp : 0 < H := by linarith
  unfold reciprocalSum
  calc
    _ ≤ ∑ h ∈ dyadicIntegers H,
        ‖∑ m ∈ dyadicIntegers M, g (h/H)*G (m/M)*exponential ((h*T/M)*F (m/M))‖ :=
      norm_sum_le _ _
    _ = ∑ h ∈ dyadicIntegers H, ‖g (h/H)‖ *
        ‖∑ m ∈ dyadicIntegers M, G (m/M)*exponential ((h*T/M)*F (m/M))‖ := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [mul_assoc, ← Finset.mul_sum, norm_mul]
    _ ≤ ∑ h ∈ dyadicIntegers H, W*B := by
      exact Finset.sum_le_sum fun h hh => mul_le_mul
        (hg.norm_le _ (dyadic_ratio_bounds hHp hh)) (hinner h hh) (norm_nonneg _) hW
    _ = ((dyadicIntegers H).card:ℝ)*(W*B) := by simp
    _ ≤ (2*H)*(W*B) := mul_le_mul_of_nonneg_right (dyadicIntegers_card_le H hH)
      (mul_nonneg hW hB)
    _ = _ := by ring

theorem elementary_double_sum (hGK : GrahamKolesnikInput) (W : ℝ) (hW : 0 < W) :
    ∃ C : ℝ, 0 < C ∧ ∀ T H M a σ b : ℝ,
      2 ≤ T → 1 ≤ H → 1 ≤ M → M ≤ Real.sqrt T →
      1/4 ≤ a → a ≤ 1 → 0 ≤ σ → σ ≤ 1 →
      ∀ g G : ℝ → ℂ, BVControl W g → BVControl W G →
      ‖reciprocalSum H M T (ReciprocalPhase.phase a σ b) g G‖ ≤
        C*H*((H*T)^((2:ℝ)/7)+1) ∧
      ‖reciprocalSum H M T (ReciprocalPhase.phase a σ b) g G‖ ≤
        C*H*((H*T/M)^((1:ℝ)/2)+T^((1:ℝ)/4)) := by
  obtain ⟨A,hA,hbound⟩ := hGK W hW
  refine ⟨4*W*A, by positivity, ?_⟩
  intro T H M a σ b hT hH hM hMT ha ha' hσ hσ' g G hg hG
  have ht : 0 < T := by linarith
  have hHp : 0 < H := by linarith
  have hMp : 0 < M := by linarith
  have htwo (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : (2:ℝ)^p ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hp1
  have hfirst : ∀ y ∈ dyadicIntegers H,
      ‖innerSum M T y a σ b G‖ ≤ 2*A*((H*T)^((2:ℝ)/7)+1) := by
    intro y hy
    have hb := dyadic_mem_bounds hy
    have hyp : 0 ≤ (y:ℝ) := by linarith [hb.1]
    have hh := (hbound T M y a σ b hT hM hMT (by linarith [hb.1]) ha ha' hσ hσ' G hG).1
    have hyT : (y:ℝ)*T ≤ 2*(H*T) := by nlinarith [hb.2]
    have hp := Real.rpow_le_rpow (show 0 ≤ (y:ℝ)*T by positivity)
      hyT (by norm_num : (0:ℝ)≤2/7)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity : 0≤H*T)] at hp
    have ht2 := htwo (2/7) (by norm_num) (by norm_num)
    have hc := mul_le_mul_of_nonneg_right ht2 (show 0 ≤ (H*T)^((2:ℝ)/7) by positivity)
    nlinarith

  have hsecond : ∀ y ∈ dyadicIntegers H,
      ‖innerSum M T y a σ b G‖ ≤ 2*A*((H*T/M)^((1:ℝ)/2)+T^((1:ℝ)/4)) := by
    intro y hy
    have hb := dyadic_mem_bounds hy
    have hyp : 0 ≤ (y:ℝ) := by linarith [hb.1]
    have hh := (hbound T M y a σ b hT hM hMT (by linarith [hb.1]) ha ha' hσ hσ' G hG).2
    have hyT : (y:ℝ)*T/M ≤ 2*(H*T/M) := by
      apply (div_le_iff₀ hMp).mpr
      have hid : 2*(H*T/M)*M=2*H*T := by field_simp <;> ring
      rw [hid]
      nlinarith [hb.2]
    have hypos : 0 ≤ (y:ℝ)*T/M := by positivity
    have hp := Real.rpow_le_rpow hypos hyT (by norm_num : (0:ℝ)≤1/2)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity : 0≤H*T/M)] at hp
    have ht2 := htwo (1/2) (by norm_num) (by norm_num)
    have hc := mul_le_mul_of_nonneg_right ht2 (show 0 ≤ (H*T/M)^((1:ℝ)/2) by positivity)
    nlinarith [Real.rpow_nonneg ht.le ((1:ℝ)/4)]
  constructor
  · have hh := norm_reciprocalSum_le hH hW.le (by positivity)
      (ReciprocalPhase.phase a σ b) g G hg hfirst
    nlinarith
  · have hh := norm_reciprocalSum_le hH hW.le (by positivity)
      (ReciprocalPhase.phase a σ b) g G hg hsecond
    nlinarith

theorem reciprocalSum_trivial {H M T W : ℝ} (hH : 1 ≤ H) (hM : 1 ≤ M)
    (hW : 0 ≤ W) (F : ℝ → ℝ) (g G : ℝ → ℂ)
    (hg : BVControl W g) (hG : BVControl W G) :
    ‖reciprocalSum H M T F g G‖ ≤ 4*W^2*H*M := by
  have hMp : 0 < M := by linarith
  have hb : ∀ h ∈ dyadicIntegers H,
      ‖∑ m ∈ dyadicIntegers M, G (m/M)*exponential ((h*T/M)*F (m/M))‖ ≤ 2*M*W := by
    intro h hh
    calc
      _ ≤ ∑ m ∈ dyadicIntegers M, ‖G (m/M)*exponential ((h*T/M)*F (m/M))‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ dyadicIntegers M, W := by
        apply Finset.sum_le_sum
        intro m hm
        simpa only [norm_mul, norm_exponential, mul_one] using
          hG.norm_le _ (dyadic_ratio_bounds hMp hm)
      _ = ((dyadicIntegers M).card:ℝ)*W := by simp
      _ ≤ 2*M*W := mul_le_mul_of_nonneg_right (dyadicIntegers_card_le M hM) hW
  have hbound := norm_reciprocalSum_le hH hW (by positivity) F g G hg hb
  nlinarith

end
end CircleDivisor.EnergyV3.ElementaryReciprocal
