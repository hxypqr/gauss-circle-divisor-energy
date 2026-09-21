import CircleDivisor.EnergyV3.ReductionFourier

/-! Choice of the finite Fourier cutoff and absorption of its dyadic logarithm.
This proves the entire §7.1 implication from the rectangle estimate, without
assuming an unproved coefficient variation or localization lemma. -/

namespace CircleDivisor.EnergyV3
noncomputable section
open scoped BigOperators

theorem dyadic_count_le_power (Y : ℕ) (hY : 1 ≤ Y) (T δ : ℝ)
    (hT : 1 ≤ T) (hYT : (Y : ℝ) ≤ T) (hδ : 0 < δ) :
    (Nat.log 2 Y + 1 : ℝ) ≤
      (1 / (δ * Real.log 2) + 1) * T ^ δ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ Nat.log 2 Y ≤ T := by
    apply le_trans _ hYT
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : Y ≠ 0)
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  rw [Real.log_pow] at hlog
  have hlogpower := Real.log_le_rpow_div (by linarith : 0 ≤ T) hδ
  have hcount : (Nat.log 2 Y : ℝ) ≤ T ^ δ / (δ * Real.log 2) := by
    rw [le_div_iff₀ (mul_pos hδ hlog2)]
    have hh : (Nat.log 2 Y : ℝ) * Real.log 2 * δ ≤ T ^ δ := by
      have hhh := mul_le_mul_of_nonneg_right (hlog.trans hlogpower) hδ.le
      have hδne : δ ≠ 0 := ne_of_gt hδ
      simpa [div_mul_cancel₀ _ hδne] using hhh
    nlinarith
  have hone : 1 ≤ T ^ δ := Real.one_le_rpow hT hδ.le
  calc
    _ ≤ T ^ δ / (δ * Real.log 2) + T ^ δ := add_le_add hcount hone
    _ = _ := by ring

theorem sawtooth_trivial_bound {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    |∑ m ∈ s, Sawtooth.psi (u m)| ≤ (s.card : ℝ) / 2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _m ∈ s, (1 / 2 : ℝ) := Finset.sum_le_sum (fun m hm => Sawtooth.abs_psi_le _)
    _ = _ := by simp; ring

/-- The exponent and the constants are quantified before every set, phase,
scale, and truncation. This is a reusable internal rectangle-to-sawtooth theorem. -/
theorem rectangle_to_sawtooth_power (hV : ClassicalInputs.VaalerApproximation)
    (θ ε C : ℝ) (hθ : 0 ≤ θ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ι : Type*} (s : Finset ι) (u : ι → ℝ)
      (T M : ℝ) (hT : 2 ≤ T) (hM : 0 ≤ M) (hMT : M ≤ T)
      (hcard : (s.card : ℝ) ≤ 2 * M),
      (∀ H : ℕ, 1 ≤ H → (H : ℝ) ≤ M / T ^ θ →
        ∀ n : ℕ, n ≤ H →
          ‖∑ i ∈ Finset.range n, frequencySum s u (H + i)‖ ≤
            C * H * T ^ (θ + ε / 2)) →
      |∑ m ∈ s, Sawtooth.psi (u m)| ≤ D * T ^ (θ + ε) := by
  obtain ⟨A, hA, hfinite⟩ := finite_fourier_reduction
  let L := 1 / ((ε / 2) * Real.log 2) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨1 + A * C * L + 2 * C, by positivity, ?_⟩
  intro ι s u T M hT hM hMT hcard hrect
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hε2 : 0 < ε / 2 := by linarith
  have hbase : 1 ≤ T ^ θ := Real.one_le_rpow hT1 hθ
  have hbasepos : 0 < T ^ θ := Real.rpow_pos_of_pos hT0 _
  have hpower : T ^ θ ≤ T ^ (θ + ε) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hpowhalf : T ^ (θ + ε / 2) ≤ T ^ (θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  by_cases hsmall : M < T ^ θ
  · have htriv := sawtooth_trivial_bound s u
    have hp : 0 ≤ T ^ (θ + ε) := Real.rpow_nonneg hT0.le _
    have hconst : 1 ≤ 1 + A * C * L + 2 * C := by
      have : 0 ≤ A * C * L + 2 * C := by positivity
      linarith
    have hh := mul_le_mul_of_nonneg_right hconst hp
    nlinarith
  have hlarge : T ^ θ ≤ M := le_of_not_gt hsmall
  let Y : ℕ := ⌊M / T ^ θ⌋₊
  have hratio : 1 ≤ M / T ^ θ := (le_div_iff₀ hbasepos).mpr (by simpa using hlarge)
  have hY : 1 ≤ Y := by exact (Nat.le_floor_iff (by positivity)).mpr (by simpa using hratio)
  have hfloor : (Y : ℝ) ≤ M / T ^ θ := Nat.floor_le (by positivity)
  have hceil : M / T ^ θ < (Y : ℝ) + 1 := Nat.lt_floor_add_one _
  have hYM : (Y : ℝ) ≤ M := hfloor.trans (div_le_self hM hbase)
  have hrectY : FiniteRectangleBound s u Y (C * T ^ (θ + ε / 2)) := by
    intro H hH hHY n hn hend
    have hHr : (H : ℝ) ≤ M / T ^ θ := (by exact_mod_cast hHY : (H : ℝ) ≤ Y).trans hfloor
    convert hrect H hH hHr n hn using 1 <;> ring
  have hbound := hfinite s u hV Y hY (C * T ^ (θ + ε / 2)) (by positivity) hrectY
  have hzero : (s.card : ℝ) / (2 * (Y + 1)) ≤ T ^ θ := by
    have hD : 0 < (Y : ℝ) + 1 := by positivity
    rw [div_le_iff₀ (mul_pos (by norm_num) hD)]
    have hMbound := (div_lt_iff₀ hbasepos).mp hceil
    nlinarith
  have hcount := dyadic_count_le_power Y hY T (ε / 2) hT1 (hYM.trans hMT) hε2
  have hmain : A * (C * T ^ (θ + ε / 2)) * (Nat.log 2 Y + 1) ≤
      A * C * L * T ^ (θ + ε) := by
    have hh := mul_le_mul_of_nonneg_left hcount
      (by positivity : 0 ≤ A * (C * T ^ (θ + ε / 2)))
    have heq : T ^ (θ + ε / 2) * T ^ (ε / 2) = T ^ (θ + ε) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring
    calc
      _ ≤ A * (C * T ^ (θ + ε / 2)) * (L * T ^ (ε / 2)) := hh
      _ = A * C * L * (T ^ (θ + ε / 2) * T ^ (ε / 2)) := by ring
      _ = _ := by rw [heq]
  have herr := mul_le_mul_of_nonneg_left hpowhalf (by positivity : 0 ≤ 2 * C)
  nlinarith

end
end CircleDivisor.EnergyV3
