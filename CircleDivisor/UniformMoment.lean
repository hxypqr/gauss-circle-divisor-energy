import CircleDivisor.Statements

/-! Compact uniformity in the moment exponent, using a finite lower grid and
the actual finite exponential sum. No spacing estimate is assumed beyond the
fixed-exponent statement explicitly supplied to the final implication. -/

namespace CircleDivisor
noncomputable section
open MeasureTheory
open scoped BigOperators

theorem dyadicIntegers_card_le (K : ℝ) (hK : 1 ≤ K) :
    ((dyadicIntegers K).card : ℝ) ≤ 2 * K := by
  have hceil : ⌈K⌉ ≤ ⌈2 * K⌉ := Int.ceil_mono (by linarith)
  have hcast : (((⌈2 * K⌉ - ⌈K⌉).toNat : ℕ) : ℝ) =
      (⌈2 * K⌉ : ℝ) - (⌈K⌉ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hceil)
  rw [dyadicIntegers, Int.card_Ico, hcast]
  have h₁ := Int.ceil_lt_add_one (2 * K)
  have h₂ := Int.le_ceil K
  linarith

theorem norm_exponential (t : ℝ) : ‖exponential t‖ = 1 := by
  unfold exponential
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t) using 1
  push_cast
  ring

theorem norm_coneSum_le (K L : ℝ) (hL : 1 ≤ L) (hLK : L ≤ K)
    (a : ℤ → ℤ → ℂ) (ha : ∀ k l, ‖a k l‖ ≤ 1) (x : Fin 3 → ℝ) :
    ‖coneSum K L a x‖ ≤ 4 * (K * L) := by
  have hK : 1 ≤ K := hL.trans hLK
  calc
    ‖coneSum K L a x‖ ≤ ∑ k ∈ dyadicIntegers K,
        ∑ l ∈ dyadicIntegers L, ‖a k l * exponential
          ((l : ℝ) * x 0 + (k : ℝ) * l * x 1 + l * Real.sqrt k * x 2)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ k ∈ dyadicIntegers K, ∑ l ∈ dyadicIntegers L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      simpa only [norm_mul, norm_exponential, mul_one] using ha k l
    _ = ((dyadicIntegers K).card : ℝ) * (dyadicIntegers L).card := by simp
    _ ≤ (2 * K) * (2 * L) :=
      mul_le_mul (dyadicIntegers_card_le K hK) (dyadicIntegers_card_le L hL)
        (by positivity) (by positivity)
    _ = 4 * (K * L) := by ring

theorem continuous_coneSum (K L : ℝ) (a : ℤ → ℤ → ℂ) :
    Continuous (coneSum K L a) := by
  unfold coneSum exponential
  fun_prop

theorem isCompact_momentBox (K : ℝ) : IsCompact (momentBox K) := by
  apply isCompact_univ_pi
  intro i
  split_ifs <;> exact isCompact_Icc

theorem integrableOn_coneMoment (K L q : ℝ) (a : ℤ → ℤ → ℂ) (hq : 0 ≤ q) :
    IntegrableOn (fun x => ‖coneSum K L a x‖ ^ q) (momentBox K) := by
  exact ContinuousOn.integrableOn_compact (isCompact_momentBox K)
    (((continuous_coneSum K L a).norm.rpow_const (fun _ => Or.inr hq)).continuousOn)

theorem coneMoment_nonneg (K L q : ℝ) (a : ℤ → ℤ → ℂ) :
    0 ≤ coneMoment K L q a := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)

theorem coneMoment_compare (K L p q d : ℝ) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hqd : q - p ≤ d)
    (a : ℤ → ℤ → ℂ) (ha : ∀ k l, ‖a k l‖ ≤ 1) :
    coneMoment K L q a ≤ (4 * (K * L)) ^ d * coneMoment K L p a := by
  have hKL : 1 ≤ K * L := by nlinarith [hL.trans hLK]
  have hbase : 1 ≤ 4 * (K * L) := by linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hpoint (x : Fin 3 → ℝ) :
      ‖coneSum K L a x‖ ^ q ≤ (4 * (K * L)) ^ d * ‖coneSum K L a x‖ ^ p := by
    have hsplit : ‖coneSum K L a x‖ ^ q =
        ‖coneSum K L a x‖ ^ p * ‖coneSum K L a x‖ ^ (q - p) := by
      rw [← Real.rpow_add_of_nonneg (norm_nonneg _) hp (sub_nonneg.mpr hpq)]
      congr 1
      ring
    rw [hsplit, mul_comm ((4 * (K * L)) ^ d)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) p)
    exact (Real.rpow_le_rpow (norm_nonneg _) (norm_coneSum_le K L hL hLK a ha x)
      (sub_nonneg.mpr hpq)).trans (Real.rpow_le_rpow_of_exponent_le hbase hqd)
  have hi := integral_mono (integrableOn_coneMoment K L q a hq)
    ((integrableOn_coneMoment K L p a hp).const_mul ((4 * (K * L)) ^ d)) hpoint
  rw [integral_const_mul] at hi
  have := mul_le_mul_of_nonneg_left hi (show 0 ≤ (2 * Real.sqrt K)⁻¹ by positivity)
  simpa only [coneMoment, mul_left_comm] using this

theorem fourTermBound_nonneg (K L q : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    0 ≤ fourTermBound K L q := by unfold fourTermBound; positivity

theorem fourTermBound_mono (K L p q : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hpq : p ≤ q) : fourTermBound K L p ≤ fourTermBound K L q := by
  have monoK {r s : ℝ} (h : r ≤ s) := Real.rpow_le_rpow_of_exponent_le hK h
  have monoL {r s : ℝ} (h : r ≤ s) := Real.rpow_le_rpow_of_exponent_le hL h
  unfold fourTermBound
  gcongr
  all_goals first
    | exact Real.rpow_le_rpow_of_exponent_le (show 1 ≤ K * L by nlinarith) (by linarith)
    | exact monoK (by linarith)
    | exact monoL (by linarith)
    | nlinarith

/-- Lower discretization: the chosen grid exponent stays in the allowed range,
is at most the requested exponent, and loses less than the prescribed mesh. -/
theorem lower_exponent_grid (q₀ q Q d : ℝ) (hd : 0 < d)
    (hq₀ : q₀ ≤ q) (hqQ : q ≤ Q) :
    ∃ j ∈ Finset.range (⌊(Q - q₀) / d⌋₊ + 1),
      q₀ ≤ q₀ + j * d ∧ q₀ + j * d ≤ q ∧ q - (q₀ + j * d) ≤ d := by
  let j := ⌊(q - q₀) / d⌋₊
  have hj : j ≤ ⌊(Q - q₀) / d⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right hqQ q₀) hd.le)
  refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), ?_, ?_, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hd.le)
  · have hh := Nat.floor_le (show 0 ≤ (q - q₀) / d by positivity)
    have hh' := (le_div_iff₀ hd).mp hh
    change q₀ + (j : ℝ) * d ≤ q
    dsimp [j] at *
    linarith
  · have hh := Nat.lt_floor_add_one ((q - q₀) / d)
    have hh' := (div_lt_iff₀ hd).mp hh
    change q - (q₀ + (j : ℝ) * d) ≤ d
    dsimp [j] at *
    nlinarith

/-- In this concrete problem, a fixed-q estimate with arbitrary epsilon DOES
imply compact uniformity. The proof uses the finite number of grid estimates,
the bound |F| <= 4KL, and monotonicity of all four explicit monomials. -/
theorem firstSpacing_uniform_of_pointwise (h : FirstSpacingStatement) :
    FirstSpacingUniformStatement := by
  intro q₀ hq₀ hq₀Q ε hε
  let d := ε / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let J := Finset.range (⌊((9 / 2 : ℝ) - q₀) / d⌋₊ + 1)
  let p : ℕ → ℝ := fun j => q₀ + j * d
  have hp (j : ℕ) (hj : j ∈ J) : 4 < p j ∧ p j ≤ 9 / 2 := by
    have hlow : q₀ ≤ p j := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hd.le)
    have hj' : j ≤ ⌊((9 / 2 : ℝ) - q₀) / d⌋₊ :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hfloor := Nat.floor_le (show 0 ≤ ((9 / 2 : ℝ) - q₀) / d by positivity)
    have hcast : (j : ℝ) ≤ (⌊((9 / 2 : ℝ) - q₀) / d⌋₊ : ℝ) := by exact_mod_cast hj'
    have hm := (le_div_iff₀ hd).mp (hcast.trans hfloor)
    exact ⟨hq₀.trans_le hlow, by dsimp [p]; linarith⟩
  have hfinite : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      (j ∈ J → ∀ K L : ℝ, 1 ≤ L → L ≤ K → ∀ a : ℤ → ℤ → ℂ,
        (∀ k l, ‖a k l‖ ≤ 1) →
          coneMoment K L (p j) a ≤ C * (K * L) ^ d * fourTermBound K L (p j)) := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨C, hC, hb⟩ := h (p j) (hp j hj).1 (hp j hj).2 d hd
      exact ⟨C, hC, fun _ => hb⟩
    · exact ⟨1, by norm_num, fun hj' => (hj hj').elim⟩
  choose C hC hb using hfinite
  let S := 1 + ∑ j ∈ J, C j
  have hS : 0 < S := by
    have : 0 ≤ ∑ j ∈ J, C j := Finset.sum_nonneg (fun j _ => (hC j).le)
    dsimp [S]
    linarith
  have hCS (j : ℕ) (hj : j ∈ J) : C j ≤ S := by
    have hh := Finset.single_le_sum (fun i _ => (hC i).le) hj
    dsimp [S]
    linarith
  refine ⟨4 ^ d * S, mul_pos (by positivity) hS, ?_⟩
  intro q hq hqQ K L hL hLK a ha
  obtain ⟨j, hj, h₀, h₁, h₂⟩ := lower_exponent_grid q₀ q (9 / 2) d hd hq hqQ
  have hjJ : j ∈ J := hj
  have hpq : p j ≤ q := h₁
  have hqd : q - p j ≤ d := h₂
  have hK : 1 ≤ K := hL.trans hLK
  have hKL : 0 < K * L := by positivity
  have hbq := fourTermBound_mono K L (p j) q hK hL hpq
  calc
    coneMoment K L q a ≤ (4 * (K * L)) ^ d * coneMoment K L (p j) a :=
      coneMoment_compare K L (p j) q d hL hLK (by linarith [((hp j hjJ).1)]) hpq hqd a ha
    _ ≤ (4 * (K * L)) ^ d * (C j * (K * L) ^ d * fourTermBound K L (p j)) :=
      mul_le_mul_of_nonneg_left (hb j hjJ K L hL hLK a ha) (by positivity)
    _ ≤ (4 * (K * L)) ^ d * (S * (K * L) ^ d * fourTermBound K L q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hCS j hjJ) (by positivity)) hbq
        (fourTermBound_nonneg K L (p j) (by positivity) (by positivity)) (by positivity)
    _ = (4 ^ d * S) * (K * L) ^ ε * fourTermBound K L q := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hKL.le]
      have he : ε = d + d := by dsimp [d]; ring
      rw [he, Real.rpow_add hKL]
      ring

theorem firstSpacing_uniform_iff_pointwise :
    FirstSpacingUniformStatement ↔ FirstSpacingStatement :=
  ⟨firstSpacing_of_uniform, firstSpacing_uniform_of_pointwise⟩

end
end CircleDivisor
