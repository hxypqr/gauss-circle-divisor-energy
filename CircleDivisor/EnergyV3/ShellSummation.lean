import CircleDivisor.EnergyV3.NeighborCount

/-! From finite metric-ball counts to a rapidly decaying kernel sum. This
supplies the shell-decomposition step in the local-density calculation. -/

namespace CircleDivisor.EnergyV3.ShellSummation
noncomputable section
open scoped BigOperators

theorem exists_shell (r : ℝ) (hr : 0 ≤ r) :
    ∃ j : ℕ, r ≤ 2 ^ j ∧ 2 ^ j ≤ 2 * (1 + r) := by
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ 1 + r by linarith)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨j + 1, by linarith, ?_⟩
  rw [pow_succ]
  linarith

def shell (r : ℝ) : ℕ := if hr : 0 ≤ r then Classical.choose (exists_shell r hr) else 0

theorem shell_bounds {r : ℝ} (hr : 0 ≤ r) :
    r ≤ 2 ^ shell r ∧ 2 ^ shell r ≤ 2 * (1 + r) := by
  unfold shell
  rw [dif_pos hr]
  exact Classical.choose_spec (exists_shell r hr)

theorem decay_le_shell {r : ℝ} (hr : 0 ≤ r) :
    ((1 + r) ^ 8)⁻¹ ≤ 256 * (1 / 256 : ℝ) ^ shell r := by
  have hh := (shell_bounds hr).2
  have hp : (2 : ℝ) ^ shell r > 0 := by positivity
  have hpow := pow_le_pow_left₀ hp.le hh 8
  have hpowid : ((2 : ℝ) ^ shell r) ^ 8 = (256 : ℝ) ^ shell r := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [mul_pow, hpowid] at hpow
  norm_num at hpow
  have hres : 1 / ((1 + r) ^ 8) ≤ 256 / (256 : ℝ) ^ shell r := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  simpa [div_eq_mul_inv, inv_pow] using hres

theorem finite_decay_sum {ι : Type*} (I : Finset ι) (r : ι → ℝ) (a b C : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hr : ∀ i ∈ I, 0 ≤ r i)
    (hcount : ∀ j : ℕ, ((I.filter (fun i => r i ≤ 2 ^ j)).card : ℝ) ≤
      C * (1 + 2 ^ j * a) * (1 + 2 ^ j * b)) :
    ∑ i ∈ I, ((1 + r i) ^ 8)⁻¹ ≤
      (256 * (64 / 63 : ℝ)) * C * (1 + a) * (1 + b) := by
  classical
  let J : Finset ℕ := I.image (fun i => shell (r i))
  have hfiber (j : ℕ) : ((I.filter (fun i => shell (r i) = j)).card : ℝ) ≤
      C * (1 + 2 ^ j * a) * (1 + 2 ^ j * b) := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (show
      I.filter (fun i => shell (r i) = j) ⊆ I.filter (fun i => r i ≤ 2 ^ j) by
        intro i hi
        obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hi, heq ▸ (shell_bounds (hr i hi)).1⟩)))
    exact hcount j
  have hf : ∑ i ∈ I, (1 / 256 : ℝ) ^ shell (r i) =
      ∑ j ∈ J, ((I.filter (fun i => shell (r i) = j)).card : ℝ) * (1 / 256 : ℝ) ^ j := by
    rw [← Finset.sum_fiberwise_of_maps_to' (s := I) (t := J)
      (fun i hi => Finset.mem_image_of_mem _ hi) (fun j => (1 / 256 : ℝ) ^ j)]
    simp
  have hs := NeighborCount.shell_series_bound ha hb
  calc
    _ ≤ ∑ i ∈ I, 256 * (1 / 256 : ℝ) ^ shell (r i) :=
      Finset.sum_le_sum (fun i hi => decay_le_shell (hr i hi))
    _ = 256 * ∑ j ∈ J, ((I.filter (fun i => shell (r i) = j)).card : ℝ) * (1 / 256 : ℝ) ^ j := by
      rw [← Finset.mul_sum, hf]
    _ ≤ 256 * ∑ j ∈ J, (C * (1 + 2 ^ j * a) * (1 + 2 ^ j * b)) * (1 / 256 : ℝ) ^ j := by
      gcongr with j hj
      exact hfiber j
    _ = 256 * C * ∑ j ∈ J, (1 / 256 : ℝ) ^ j * (1 + 2 ^ j * a) * (1 + 2 ^ j * b) := by
      simp_rw [show ∀ j : ℕ, (C * (1 + 2 ^ j * a) * (1 + 2 ^ j * b)) * (1 / 256 : ℝ) ^ j =
        C * ((1 / 256 : ℝ) ^ j * (1 + 2 ^ j * a) * (1 + 2 ^ j * b)) by intro j; ring]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 256 * C * ∑' j : ℕ, (1 / 256 : ℝ) ^ j * (1 + 2 ^ j * a) * (1 + 2 ^ j * b) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hs.1.sum_le_tsum J (fun j _ => by positivity)
    _ ≤ (256 * (64 / 63 : ℝ)) * C * (1 + a) * (1 + b) := by
      have hh := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ 256 * C by positivity)
      nlinarith

end
end CircleDivisor.EnergyV3.ShellSummation
