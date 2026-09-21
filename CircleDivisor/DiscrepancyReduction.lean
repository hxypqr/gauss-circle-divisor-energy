import CircleDivisor.ClassicalInputs
import CircleDivisor.Hyperbola
import CircleDivisor.LatticeDomain

/-!
# Arithmetic discrepancy reductions in Section 7

The statements here concern the actual summatory divisor function from `Statements`.
Only the explicitly named classical harmonic expansion is supplied as an input.
-/

namespace CircleDivisor.DiscrepancyReduction
noncomputable section
open scoped BigOperators

theorem icc_one_eq_ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem divisorSummatory_eq_sum_div (X : ℝ) :
    divisorSummatory X = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ((⌊X⌋₊ / a : ℕ) : ℝ) := by
  unfold divisorSummatory
  rw [icc_one_eq_ioc_zero]
  have h := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div ⌊X⌋₊
  simp only [ArithmeticFunction.sigma_zero_apply] at h
  exact_mod_cast h

theorem hyperbola_row (N a : ℕ) (ha : 1 ≤ a) :
    (∑ b ∈ Finset.Icc 1 N, if a * b ≤ N then (1 : ℝ) else 0) = (N / a : ℕ) := by
  rw [← Finset.sum_filter]
  have hset : (Finset.Icc 1 N).filter (fun b => a * b ≤ N) = Finset.Icc 1 (N / a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hh : b ≤ N / a ↔ a * b ≤ N := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [Nat.mul_comm]
    rw [hh]
    constructor
    · tauto
    · rintro ⟨hb, hab⟩
      refine ⟨⟨hb, ?_⟩, hab⟩
      nlinarith
  rw [hset]
  simp

theorem truncated_sum (N U : ℕ) (hUN : U ≤ N) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 N, if a ≤ U then f a else 0) = ∑ a ∈ Finset.Icc 1 U, f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Exact Dirichlet hyperbola identity, before converting integer division to floors. -/
theorem sum_div_hyperbola (N U : ℕ) (hU : 1 ≤ U)
    (hlo : U ^ 2 ≤ N) (hhi : N < (U + 1) ^ 2) :
    (∑ a ∈ Finset.Icc 1 N, (N / a : ℕ) : ℝ) =
      2 * (∑ a ∈ Finset.Icc 1 U, (N / a : ℕ) : ℝ) - (U : ℝ) ^ 2 := by
  have hUN : U ≤ N := by nlinarith
  have hrow := Hyperbola.symmetric_hyperbola (Finset.Icc 1 N) (fun _ _ => (1 : ℝ))
    N U (fun _ _ => rfl) hlo hhi
  have hfull : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if a * b ≤ N then (1 : ℝ) else 0) = ∑ a ∈ Finset.Icc 1 N, ((N / a : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hyperbola_row N a (Finset.mem_Icc.mp ha).1
  have hbranch : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if a ≤ U ∧ a * b ≤ N then (1 : ℝ) else 0) = ∑ a ∈ Finset.Icc 1 U, ((N / a : ℕ) : ℝ) := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N, if a ≤ U then ((N / a : ℕ) : ℝ) else (0 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases haU : a ≤ U
        · simp only [haU, true_and, if_true]
          exact hyperbola_row N a (Finset.mem_Icc.mp ha).1
        · simp [haU]
      _ = _ := truncated_sum N U hUN _
  have hbox : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if a ≤ U ∧ b ≤ U then (1 : ℝ) else 0) = (U : ℝ) ^ 2 := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N, if a ≤ U then (U : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases haU : a ≤ U
        · simp only [haU, true_and, if_true]
          rw [truncated_sum N U hUN]
          simp
        · simp [haU]
      _ = _ := by rw [truncated_sum N U hUN]; simp [pow_two]
  rw [hfull, hbranch, hbox] at hrow
  exact hrow

/-- The exact floor hyperbola formula for the actual divisor summatory function. -/
theorem divisorSummatory_hyperbola (X : ℝ) (U : ℕ) (hU : 1 ≤ U)
    (hlo : (U : ℝ) ^ 2 ≤ X) (hhi : X < (U + 1 : ℕ) ^ 2) :
    divisorSummatory X =
      2 * (∑ a ∈ Finset.Icc 1 U, (⌊X / a⌋ : ℤ) : ℝ) - (U : ℝ) ^ 2 := by
  have hX : 0 ≤ X := le_trans (sq_nonneg _) hlo
  have hNlo : U ^ 2 ≤ ⌊X⌋₊ := by exact Nat.le_floor (by exact_mod_cast hlo)
  have hNhi : ⌊X⌋₊ < (U + 1) ^ 2 := by exact (Nat.floor_lt hX).mpr (by exact_mod_cast hhi)
  rw [divisorSummatory_eq_sum_div, sum_div_hyperbola _ U hU hNlo hNhi]
  congr 2
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Nat.floor_div_natCast]
  exact natCast_floor_eq_intCast_floor (show 0 ≤ X / (a : ℝ) by positivity)

/-- Exact error term after the floor identity and harmonic sum have been substituted. -/
theorem divisorError_sawtooth_exact (X : ℝ) (U : ℕ) (hU : 1 ≤ U)
    (hlo : (U : ℝ) ^ 2 ≤ X) (hhi : X < (U + 1 : ℕ) ^ 2) :
    divisorError X = -2 * (∑ a ∈ Finset.Icc 1 U, Sawtooth.psi (X / a)) +
      (2 * X * (harmonic U : ℝ) - U - (U : ℝ) ^ 2 - X * Real.log X -
        (2 * Real.eulerMascheroniConstant - 1) * X) := by
  unfold divisorError
  rw [divisorSummatory_hyperbola X U hU hlo hhi]
  simp_rw [Sawtooth.floor_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hh : (∑ a ∈ Finset.Icc 1 U, X / (a : ℝ)) = X * (harmonic U : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      div_eq_mul_inv, Finset.mul_sum]
  rw [hh]
  simp
  ring

/-- A quadratic logarithmic remainder bound with an elementary proof. -/
theorem log_remainder_bounds {X U : ℝ} (hU : 0 < U) (hlo : U ^ 2 ≤ X) :
    -(X - U ^ 2) ^ 2 / U ^ 2 ≤ X - U ^ 2 - X * Real.log (X / U ^ 2) ∧
      X - U ^ 2 - X * Real.log (X / U ^ 2) ≤ 0 := by
  have hU2 : 0 < U ^ 2 := sq_pos_of_pos hU
  have hX : 0 < X := lt_of_lt_of_le hU2 hlo
  have hz : 0 < X / U ^ 2 := div_pos hX hU2
  have hu := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hz) hX.le
  have hl := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hz) hX.le
  have hupper : X * (X / U ^ 2 - 1) = (X - U ^ 2) + (X - U ^ 2) ^ 2 / U ^ 2 := by
    field_simp
    ring
  have hlower : X * (1 - (X / U ^ 2)⁻¹) = X - U ^ 2 := by
    field_simp
  rw [hupper] at hu
  rw [hlower] at hl
  rw [neg_div]
  constructor <;> linarith

/-- The analytic cancellation in Section 7.2, with an explicit absolute constant. -/
theorem divisor_remainder_bound (C X : ℝ) (U : ℕ) (hC : 0 ≤ C) (hU : 1 ≤ U)
    (hlo : (U : ℝ) ^ 2 ≤ X) (hhi : X < (U + 1 : ℕ) ^ 2)
    (hH : |(harmonic U : ℝ) - Real.log U - Real.eulerMascheroniConstant -
      1 / (2 * U)| ≤ C / (U : ℝ) ^ 2) :
    |2 * X * (harmonic U : ℝ) - U - (U : ℝ) ^ 2 - X * Real.log X -
      (2 * Real.eulerMascheroniConstant - 1) * X| ≤ 12 + 8 * C := by
  have hUreal : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hUpos : (0 : ℝ) < U := by linarith
  have hUne : (U : ℝ) ≠ 0 := ne_of_gt hUpos
  have hU2 : 0 < (U : ℝ) ^ 2 := sq_pos_of_pos hUpos
  have hX : 0 < X := lt_of_lt_of_le hU2 hlo
  have hhi' : X < ((U : ℝ) + 1) ^ 2 := by exact_mod_cast hhi
  have hgap := Sawtooth.floor_sqrt_remainder hUreal hlo hhi'
  have hratio : X / (U : ℝ) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ hU2]
    nlinarith
  have hlog := log_remainder_bounds hUpos hlo
  rw [neg_div] at hlog
  have hgap2 : (X - (U : ℝ) ^ 2) ^ 2 / (U : ℝ) ^ 2 ≤ 9 := by
    have heq : (X - (U : ℝ) ^ 2) ^ 2 / (U : ℝ) ^ 2 =
        ((X - (U : ℝ) ^ 2) / U) ^ 2 := by rw [div_pow]
    rw [heq]
    nlinarith [hgap.1, hgap.2]
  have hlogabs : |X - (U : ℝ) ^ 2 - X * Real.log (X / (U : ℝ) ^ 2)| ≤ 9 := by
    rw [abs_le]
    constructor <;> linarith
  have hlinabs : |(X - (U : ℝ) ^ 2) / U| ≤ 3 := by
    rw [abs_of_nonneg hgap.1]
    exact hgap.2.le
  have hHabs : |2 * X * ((harmonic U : ℝ) - Real.log U -
      Real.eulerMascheroniConstant - 1 / (2 * U))| ≤ 8 * C := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * X)]
    calc
      _ ≤ 2 * X * (C / (U : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hH (by positivity)
      _ = 2 * (X / (U : ℝ) ^ 2) * C := by ring
      _ ≤ 8 * C := by nlinarith
  have hlogs : Real.log (X / (U : ℝ) ^ 2) = Real.log X - 2 * Real.log U := by
    rw [Real.log_div (ne_of_gt hX) (pow_ne_zero _ hUne), Real.log_pow]
    norm_num
  have hexact : 2 * X * (harmonic U : ℝ) - U - (U : ℝ) ^ 2 - X * Real.log X -
      (2 * Real.eulerMascheroniConstant - 1) * X =
      (X - (U : ℝ) ^ 2 - X * Real.log (X / (U : ℝ) ^ 2)) +
      (X - (U : ℝ) ^ 2) / U +
      2 * X * ((harmonic U : ℝ) - Real.log U - Real.eulerMascheroniConstant -
        1 / (2 * U)) := by
    rw [hlogs]
    field_simp
    ring
  rw [hexact]
  calc
    _ ≤ |X - (U : ℝ) ^ 2 - X * Real.log (X / (U : ℝ) ^ 2)| +
        |(X - (U : ℝ) ^ 2) / U| +
        |2 * X * ((harmonic U : ℝ) - Real.log U - Real.eulerMascheroniConstant -
          1 / (2 * U))| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 12 + 8 * C := by linarith

theorem floor_sqrt_conditions (X : ℝ) (hX : 1 ≤ X) :
    1 ≤ ⌊Real.sqrt X⌋₊ ∧ (⌊Real.sqrt X⌋₊ : ℝ) ^ 2 ≤ X ∧
      X < (⌊Real.sqrt X⌋₊ + 1 : ℕ) ^ 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ X by linarith)
  have hs0 := Real.sqrt_nonneg X
  have hlo := Nat.floor_le hs0
  have hhi := Nat.lt_floor_add_one (Real.sqrt X)
  have hfloor0 : (0 : ℝ) ≤ ⌊Real.sqrt X⌋₊ := by positivity
  refine ⟨Nat.le_floor ?_, ?_, ?_⟩
  · norm_num
    nlinarith
  · nlinarith
  · push_cast
    nlinarith

/-- Section 7.2, equation (7.4): uniform in every real X ≥ 1, including integer endpoints.
The only external premise is the stated classical harmonic expansion.
-/
theorem divisorError_sawtooth (hH : ClassicalInputs.HarmonicExpansion) :
    ∃ B : ℝ, 0 < B ∧ ∀ X : ℝ, 1 ≤ X →
      |divisorError X + 2 * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊,
        Sawtooth.psi (X / a))| ≤ B := by
  obtain ⟨C, hC, hH⟩ := hH
  refine ⟨12 + 8 * C, by positivity, ?_⟩
  intro X hX
  obtain ⟨hU, hlo, hhi⟩ := floor_sqrt_conditions X hX
  rw [divisorError_sawtooth_exact X _ hU hlo hhi]
  have hcancel (S R : ℝ) : -2 * S + R + 2 * S = R := by ring
  rw [hcancel]
  exact divisor_remainder_bound C X _ hC.le hU hlo hhi (hH _ hU)

/-- The finite Vaaler error can be summed without replacing the Fourier h-sum
by a sum of absolute values. This is the exact starting inequality in §7.1. -/
theorem vaaler_sum_error {ι : Type*} (hV : ClassicalInputs.VaalerApproximation)
    (I : Finset ι) (u : ι → ℝ) (Y : ℕ) (hY : 1 ≤ Y) :
    |(∑ m ∈ I, Sawtooth.psi (u m)) -
        ∑ m ∈ I, ClassicalInputs.vaalerApproximation Y (u m)| ≤
      (I.card : ℝ) / (2 * (Y + 1)) +
        (∑ h ∈ Finset.Icc 1 Y, (1 - (h : ℝ) / (Y + 1)) *
          ∑ m ∈ I, Real.cos (2 * Real.pi * h * u m)) / (Y + 1) := by
  calc
    _ = |∑ m ∈ I, (Sawtooth.psi (u m) - ClassicalInputs.vaalerApproximation Y (u m))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ m ∈ I, |Sawtooth.psi (u m) - ClassicalInputs.vaalerApproximation Y (u m)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ I, ClassicalInputs.fejerRemainder Y (u m) := by
      exact Finset.sum_le_sum fun m _ => hV Y hY (u m)
    _ = _ := by
      unfold ClassicalInputs.fejerRemainder
      have hswap : (∑ m ∈ I, ∑ h ∈ Finset.Icc 1 Y,
          (1 - (h : ℝ) / (Y + 1)) * Real.cos (2 * Real.pi * h * u m)) =
          ∑ h ∈ Finset.Icc 1 Y, (1 - (h : ℝ) / (Y + 1)) *
            ∑ m ∈ I, Real.cos (2 * Real.pi * h * u m) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      rw [← Finset.sum_div, Finset.sum_add_distrib, hswap]
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
      simp only [mul_comm, mul_left_comm]

/-- The signed main Fourier sum, with the h-sum kept intact. -/
theorem vaaler_sum_eq {ι : Type*} (I : Finset ι) (u : ι → ℝ) (Y : ℕ) :
    (∑ m ∈ I, ClassicalInputs.vaalerApproximation Y (u m)) =
      -(∑ h ∈ Finset.Icc 1 Y,
        (ClassicalInputs.vaalerWeight ((h : ℝ) / (Y + 1)) / (Real.pi * h)) *
          ∑ m ∈ I, Real.sin (2 * Real.pi * h * u m)) := by
  unfold ClassicalInputs.vaalerApproximation
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The full finite starting bound of Lemma 7.1. Both Fourier double sums preserve
cancellation in h; the cosine error sum has not been replaced by absolute values. -/
theorem sawtooth_sum_le_fourier {ι : Type*} (hV : ClassicalInputs.VaalerApproximation)
    (I : Finset ι) (u : ι → ℝ) (Y : ℕ) (hY : 1 ≤ Y) :
    |∑ m ∈ I, Sawtooth.psi (u m)| ≤
      |∑ h ∈ Finset.Icc 1 Y,
        (ClassicalInputs.vaalerWeight ((h : ℝ) / (Y + 1)) / (Real.pi * h)) *
          ∑ m ∈ I, Real.sin (2 * Real.pi * h * u m)| +
      ((I.card : ℝ) / (2 * (Y + 1)) +
        (∑ h ∈ Finset.Icc 1 Y, (1 - (h : ℝ) / (Y + 1)) *
          ∑ m ∈ I, Real.cos (2 * Real.pi * h * u m)) / (Y + 1)) := by
  have he := vaaler_sum_error hV I u Y hY
  have ht := abs_add_le
    (∑ m ∈ I, ClassicalInputs.vaalerApproximation Y (u m))
    ((∑ m ∈ I, Sawtooth.psi (u m)) - ∑ m ∈ I, ClassicalInputs.vaalerApproximation Y (u m))
  have hA : |∑ m ∈ I, ClassicalInputs.vaalerApproximation Y (u m)| =
      |∑ h ∈ Finset.Icc 1 Y,
        (ClassicalInputs.vaalerWeight ((h : ℝ) / (Y + 1)) / (Real.pi * h)) *
          ∑ m ∈ I, Real.sin (2 * Real.pi * h * u m)| := by
    rw [vaaler_sum_eq, abs_neg]
  rw [← add_sub_assoc, add_sub_cancel_left, hA] at ht
  exact ht.trans (add_le_add le_rfl he)

def latticeNorm (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 + p.2 ^ 2).toNat

theorem latticeNorm_intCast (p : ℤ × ℤ) : (latticeNorm p : ℤ) = p.1 ^ 2 + p.2 ^ 2 := by
  exact Int.toNat_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem latticeNorm_realCast (p : ℤ × ℤ) :
    (latticeNorm p : ℝ) = (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  exact_mod_cast latticeNorm_intCast p

/-- The disk is partitioned by its actual integer squared-radius fibers. -/
theorem circleCount_eq_sum_twoSquares (X : ℝ) (hX : 0 ≤ X) :
    circleCount X = ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, ClassicalInputs.twoSquaresCount n := by
  classical
  let S := (circle_lattice_set_finite X).toFinset
  have hmem (p : ℤ × ℤ) : p ∈ S ↔ (latticeNorm p : ℝ) ≤ X := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, latticeNorm_realCast]
  have hmap : ∀ p ∈ S, latticeNorm p ∈ Finset.Icc 0 ⌊X⌋₊ := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor ((hmem p).mp hp)⟩
  have hfiber : ∀ n ∈ Finset.Icc 0 ⌊X⌋₊,
      (S.filter (fun p => latticeNorm p = n)).card = ClassicalInputs.twoSquaresCount n := by
    intro n hn
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hX)
    have hset : (↑(S.filter (fun p => latticeNorm p = n)) : Set (ℤ × ℤ)) =
        {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)} := by
      ext p
      simp only [Finset.mem_coe, Finset.mem_filter, hmem, Set.mem_setOf_eq]
      have heq : latticeNorm p = n ↔ p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
        rw [← latticeNorm_intCast]
        exact Nat.cast_inj.symm
      constructor
      · exact fun hp => heq.mp hp.2
      · intro hp
        have hn' := heq.mpr hp
        exact ⟨hn' ▸ hnX, hn'⟩
    rw [← Set.ncard_coe_finset, hset]
    rfl
  calc
    circleCount X = S.card := Set.ncard_eq_toFinset_card _ (circle_lattice_set_finite X)
    _ = ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (S.filter (fun p => latticeNorm p = n)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = _ := Finset.sum_congr rfl hfiber

theorem twoSquaresCount_zero : ClassicalInputs.twoSquaresCount 0 = 1 := by
  unfold ClassicalInputs.twoSquaresCount
  have hset : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (0 : ℤ)} = {(0, 0)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.ext_iff]
    constructor
    · intro hp
      constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    · rintro ⟨h₁, h₂⟩
      simp [h₁, h₂]
  simp only [Nat.cast_zero, hset, Set.ncard_singleton]

/-- Equation (7.5) from the coefficient form of the external two-squares theorem. -/
theorem circleCount_character_divisors (h2 : ClassicalInputs.TwoSquaresIdentity)
    (X : ℝ) (hX : 0 ≤ X) :
    (circleCount X : ℝ) = 1 + 4 *
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ∑ d ∈ n.divisors, (Sawtooth.chi4 d : ℝ) := by
  rw [circleCount_eq_sum_twoSquares X hX]
  have hsplit : ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, ClassicalInputs.twoSquaresCount n =
      ClassicalInputs.twoSquaresCount 0 +
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ClassicalInputs.twoSquaresCount n := by
    have hset : Finset.Icc 0 ⌊X⌋₊ = insert 0 (Finset.Icc 1 ⌊X⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
  rw [hsplit, twoSquaresCount_zero]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact_mod_cast h2 n (Finset.mem_Icc.mp hn).1

theorem hyperbola_weighted_row (N a : ℕ) (ha : 1 ≤ a) (f : ℕ → ℝ) :
    (∑ b ∈ Finset.Icc 1 N, if a * b ≤ N then f b else 0) =
      ∑ b ∈ Finset.Icc 1 (N / a), f b := by
  rw [← Finset.sum_filter]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hh : b ≤ N / a ↔ a * b ≤ N := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
  rw [hh]
  constructor
  · tauto
  · rintro ⟨hb, hab⟩
    refine ⟨⟨hb, ?_⟩, hab⟩
    nlinarith

/-- The weighted hyperbola identity, with both branches evaluated as actual sums. -/
theorem weighted_sum_div_hyperbola (N U : ℕ) (hU : 1 ≤ U)
    (hlo : U ^ 2 ≤ N) (hhi : N < (U + 1) ^ 2) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 N, f a * (N / a : ℕ)) =
      (∑ a ∈ Finset.Icc 1 U, f a * (N / a : ℕ)) +
      (∑ b ∈ Finset.Icc 1 U, ∑ a ∈ Finset.Icc 1 (N / b), f a) -
      U * (∑ a ∈ Finset.Icc 1 U, f a) := by
  have hUN : U ≤ N := by nlinarith
  have hrow := Hyperbola.weighted_hyperbola (Finset.Icc 1 N) (Finset.Icc 1 N)
    (fun a _ => f a) N U hlo hhi
  have heval (a : ℕ) (ha : 1 ≤ a) :
      (∑ b ∈ Finset.Icc 1 N, if a * b ≤ N then f a else 0) = f a * (N / a : ℕ) := by
    calc
      _ = f a * (∑ b ∈ Finset.Icc 1 N, if a * b ≤ N then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        split_ifs <;> simp
      _ = _ := by rw [hyperbola_row N a ha]
  have hfull : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if a * b ≤ N then f a else 0) = ∑ a ∈ Finset.Icc 1 N, f a * (N / a : ℕ) := by
    exact Finset.sum_congr rfl fun a ha => heval a (Finset.mem_Icc.mp ha).1
  have hbranch1 : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if a ≤ U ∧ a * b ≤ N then f a else 0) = ∑ a ∈ Finset.Icc 1 U, f a * (N / a : ℕ) := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N, if a ≤ U then f a * (N / a : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases haU : a ≤ U
        · simp only [haU, true_and, if_true]
          exact heval a (Finset.mem_Icc.mp ha).1
        · simp [haU]
      _ = _ := truncated_sum N U hUN _
  have hbranch2 : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if b ≤ U ∧ a * b ≤ N then f a else 0) =
      ∑ b ∈ Finset.Icc 1 U, ∑ a ∈ Finset.Icc 1 (N / b), f a := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ b ∈ Finset.Icc 1 N, if b ≤ U then (∑ a ∈ Finset.Icc 1 (N / b), f a) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hbU : b ≤ U
        · simp only [hbU, true_and, if_true]
          simp_rw [Nat.mul_comm _ b]
          exact hyperbola_weighted_row N b (Finset.mem_Icc.mp hb).1 f
        · simp [hbU]
      _ = _ := truncated_sum N U hUN _
  have hbox : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if a ≤ U ∧ b ≤ U then f a else 0) = U * (∑ a ∈ Finset.Icc 1 U, f a) := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N, if a ≤ U then (U : ℝ) * f a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases haU : a ≤ U
        · simp only [haU, true_and, if_true]
          rw [truncated_sum N U hUN]
          simp
        · simp [haU]
      _ = _ := by rw [truncated_sum N U hUN, Finset.mul_sum]
  rw [hfull, hbranch1, hbranch2, hbox] at hrow
  exact hrow

def chiArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => (Sawtooth.chi4 n : ℝ), by norm_num [Sawtooth.chi4]⟩

theorem character_divisors_eq_sum_div (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (Sawtooth.chi4 d : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N, (Sawtooth.chi4 d : ℝ) * (N / d : ℕ) := by
  have hh := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum chiArithmetic N
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at hh
  simpa only [chiArithmetic, ArithmeticFunction.coe_mk, icc_one_eq_ioc_zero] using hh

theorem partialSum_eq_sum_Icc (N : ℕ) :
    (Sawtooth.partialSum N : ℝ) = ∑ d ∈ Finset.Icc 1 N, (Sawtooth.chi4 d : ℝ) := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold Sawtooth.partialSum
  rw [hset, Finset.sum_insert (by simp)]
  simp [Sawtooth.chi4]

/-- Equation (7.6), for the actual disk count and exact character partial sums. -/
theorem circleCount_hyperbola (h2 : ClassicalInputs.TwoSquaresIdentity)
    (X : ℝ) (U : ℕ) (hU : 1 ≤ U)
    (hlo : (U : ℝ) ^ 2 ≤ X) (hhi : X < (U + 1 : ℕ) ^ 2) :
    (circleCount X : ℝ) = 1 + 4 *
      ((∑ d ∈ Finset.Icc 1 U, (Sawtooth.chi4 d : ℝ) * (⌊X / d⌋ : ℤ)) +
      (∑ m ∈ Finset.Icc 1 U, (Sawtooth.partialSum ⌊X / m⌋₊ : ℝ)) -
      U * (Sawtooth.partialSum U : ℝ)) := by
  have hX : 0 ≤ X := le_trans (sq_nonneg _) hlo
  have hNlo : U ^ 2 ≤ ⌊X⌋₊ := by exact Nat.le_floor (by exact_mod_cast hlo)
  have hNhi : ⌊X⌋₊ < (U + 1) ^ 2 := by exact (Nat.floor_lt hX).mpr (by exact_mod_cast hhi)
  rw [circleCount_character_divisors h2 X hX, character_divisors_eq_sum_div,
    weighted_sum_div_hyperbola _ U hU hNlo hNhi, ← partialSum_eq_sum_Icc]
  simp_rw [← partialSum_eq_sum_Icc, ← Nat.floor_div_natCast]
  congr 4
  apply Finset.sum_congr rfl
  intro d hd
  rw [natCast_floor_eq_intCast_floor (show 0 ≤ X / (d : ℝ) by positivity)]

theorem partialSum_floor_eq_floorDifference (u : ℝ) (hu : 0 ≤ u) :
    (Sawtooth.partialSum ⌊u⌋₊ : ℝ) = Sawtooth.floorDifference u := by
  rw [Sawtooth.partialSum_formula]
  unfold Sawtooth.floorDifference
  have h₃ : (⌊(u + 3) / 4⌋ : ℝ) = ((⌊u⌋₊ + 3) / 4 : ℕ) := by
    rw [← natCast_floor_eq_intCast_floor (show 0 ≤ (u + 3) / 4 by positivity),
      Nat.floor_div_ofNat, Nat.floor_add_ofNat hu]
  have h₁ : (⌊(u + 1) / 4⌋ : ℝ) = ((⌊u⌋₊ + 1) / 4 : ℕ) := by
    rw [← natCast_floor_eq_intCast_floor (show 0 ≤ (u + 1) / 4 by positivity),
      Nat.floor_div_ofNat, Nat.floor_add_one hu]
  rw [h₃, h₁]
  push_cast
  rfl

def betaSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (Sawtooth.chi4 d : ℝ) / d

def betaB (N : ℕ) : ℝ := 1 / 2 - Sawtooth.partialSum N

def betaC (N : ℕ) : ℝ := (Sawtooth.chi4 N : ℝ) / 2

def betaWeight (N : ℕ) : ℝ := 1 / ((N : ℝ) * (N + 1))

def betaCorrected (N : ℕ) : ℝ := betaSum N + betaB N / N + betaC N * betaWeight N

theorem partialSum_succ (N : ℕ) :
    Sawtooth.partialSum (N + 1) = Sawtooth.partialSum N + Sawtooth.chi4 (N + 1) := by
  exact Finset.sum_range_succ _ _

theorem betaSum_succ (N : ℕ) :
    betaSum (N + 1) = betaSum N + (Sawtooth.chi4 (N + 1) : ℝ) / (N + 1) := by
  unfold betaSum
  have hset : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  push_cast
  ring

/-- The second bounded discrete primitive responsible for the extra power in (7.8). -/
theorem chi4_difference (N : ℕ) :
    Sawtooth.chi4 (N + 1) - Sawtooth.chi4 N = 1 - 2 * Sawtooth.partialSum N := by
  rw [Sawtooth.partialSum_formula]
  unfold Sawtooth.chi4
  split_ifs <;> omega

theorem betaC_bounds (N : ℕ) : -(1 / 2) ≤ betaC N ∧ betaC N ≤ 1 / 2 := by
  have h : |(Sawtooth.chi4 N : ℝ)| ≤ 1 := by exact_mod_cast Sawtooth.chi4_abs_le N
  rw [abs_le] at h
  unfold betaC
  constructor <;> linarith

theorem betaB_abs_le (N : ℕ) : |betaB N| ≤ 1 / 2 := by
  rcases Sawtooth.partialSum_zero_or_one N with h | h
  all_goals norm_num [betaB, h]

theorem betaWeight_nonneg (N : ℕ) : 0 ≤ betaWeight N := by unfold betaWeight; positivity

theorem betaWeight_succ_le (N : ℕ) (hN : 1 ≤ N) : betaWeight (N + 1) ≤ betaWeight N := by
  unfold betaWeight
  push_cast
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem betaCorrected_succ (N : ℕ) (hN : 1 ≤ N) :
    betaCorrected (N + 1) - betaCorrected N =
      betaC (N + 1) * (betaWeight (N + 1) - betaWeight N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hchi : (Sawtooth.chi4 (N + 1) : ℝ) =
      Sawtooth.chi4 N + 1 - 2 * Sawtooth.partialSum N := by
    have hh : (Sawtooth.chi4 (N + 1) : ℝ) - Sawtooth.chi4 N =
        1 - 2 * Sawtooth.partialSum N := by exact_mod_cast chi4_difference N
    linarith
  unfold betaCorrected
  rw [betaSum_succ]
  unfold betaB betaC betaWeight
  rw [partialSum_succ]
  push_cast
  rw [hchi]
  field_simp
  ring

theorem beta_lower_monotone : MonotoneOn (fun N => betaCorrected N - betaWeight N / 2)
    (Set.Ici 1) := by
  apply monotoneOn_nat_Ici_of_le_succ
  intro N hN
  have hr := betaCorrected_succ N hN
  have hw := betaWeight_succ_le N hN
  have hc := betaC_bounds (N + 1)
  nlinarith

theorem beta_upper_antitone : AntitoneOn (fun N => betaCorrected N + betaWeight N / 2)
    (Set.Ici 1) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro N hN
  have hr := betaCorrected_succ N hN
  have hw := betaWeight_succ_le N hN
  have hc := betaC_bounds (N + 1)
  nlinarith

open Filter
open scoped Topology

theorem betaWeight_tendsto : Tendsto betaWeight atTop (𝓝 0) := by
  have h₁ : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h₂ : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun N => betaWeight N) atTop (𝓝 0)
  simpa only [betaWeight, ← one_div_mul_one_div, mul_zero] using h₁.mul h₂

theorem betaB_div_tendsto : Tendsto (fun N : ℕ => betaB N / N) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ => (1 / 2 : ℝ) / N)
  · intro N
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ N by positivity)]
    exact div_le_div_of_nonneg_right (betaB_abs_le N) (Nat.cast_nonneg N)
  · exact tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)

theorem betaC_mul_weight_tendsto : Tendsto (fun N : ℕ => betaC N * betaWeight N) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ => (1 / 2 : ℝ) * betaWeight N)
  · intro N
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (betaWeight_nonneg N)]
    apply mul_le_mul_of_nonneg_right _ (betaWeight_nonneg N)
    exact abs_le.mpr (betaC_bounds N)
  · simpa using betaWeight_tendsto.const_mul (1 / 2 : ℝ)

theorem betaCorrected_tendsto (hβ : ClassicalInputs.BetaAtOne) :
    Tendsto betaCorrected atTop (𝓝 (Real.pi / 4)) := by
  change Tendsto (fun N => betaCorrected N) atTop (𝓝 (Real.pi / 4))
  simpa only [betaCorrected, betaSum, add_zero] using
    (hβ.add betaB_div_tendsto).add betaC_mul_weight_tendsto

/-- Equation (7.8), with constant 1: the beta tail expansion is proved internally
from the ordered beta value. It is not an additional external premise. -/
theorem beta_tail_bound (hβ : ClassicalInputs.BetaAtOne) (U : ℕ) (hU : 1 ≤ U) :
    |Real.pi / 4 - betaSum U - (1 / 2 - (Sawtooth.partialSum U : ℝ)) / U| ≤
      1 / (U : ℝ) ^ 2 := by
  have hlimL : Tendsto (fun N => betaCorrected N - betaWeight N / 2) atTop (𝓝 (Real.pi / 4)) := by
    simpa using (betaCorrected_tendsto hβ).sub (betaWeight_tendsto.div_const 2)
  have hlimR : Tendsto (fun N => betaCorrected N + betaWeight N / 2) atTop (𝓝 (Real.pi / 4)) := by
    simpa using (betaCorrected_tendsto hβ).add (betaWeight_tendsto.div_const 2)
  have hl : betaCorrected U - betaWeight U / 2 ≤ Real.pi / 4 := by
    apply ge_of_tendsto hlimL
    filter_upwards [eventually_ge_atTop U] with N hN
    exact beta_lower_monotone hU (show 1 ≤ N from le_trans hU hN) hN
  have hr : Real.pi / 4 ≤ betaCorrected U + betaWeight U / 2 := by
    apply le_of_tendsto hlimR
    filter_upwards [eventually_ge_atTop U] with N hN
    exact beta_upper_antitone hU (show 1 ≤ N from le_trans hU hN) hN
  have hw := betaWeight_nonneg U
  have hc := betaC_bounds U
  have hdiff : |Real.pi / 4 - betaSum U - betaB U / U| ≤ betaWeight U := by
    unfold betaCorrected at hl hr
    rw [abs_le]
    constructor <;> nlinarith
  refine hdiff.trans ?_
  unfold betaWeight
  have hUpos : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The three concrete reciprocal sawtooth sums on the right of (7.9). -/
def circleSawtooth (X : ℝ) (U : ℕ) : ℝ :=
  -4 * (∑ d ∈ Finset.Icc 1 U, (Sawtooth.chi4 d : ℝ) * Sawtooth.psi (X / d)) +
    4 * (∑ m ∈ Finset.Icc 1 U,
      (Sawtooth.psi (X / (4 * m) + 1 / 4) - Sawtooth.psi (X / (4 * m) + 3 / 4)))

theorem circleError_sawtooth_exact (h2 : ClassicalInputs.TwoSquaresIdentity)
    (X : ℝ) (U : ℕ) (hU : 1 ≤ U)
    (hlo : (U : ℝ) ^ 2 ≤ X) (hhi : X < (U + 1 : ℕ) ^ 2) :
    circleError X = circleSawtooth X U +
      (1 - 2 * (Sawtooth.partialSum U : ℝ) +
        4 * (-(X / U) * betaB U + U * betaB U) -
        4 * X * (Real.pi / 4 - betaSum U - betaB U / U)) := by
  have hX : 0 ≤ X := le_trans (sq_nonneg _) hlo
  have hUne : (U : ℝ) ≠ 0 := by exact_mod_cast (show U ≠ 0 by omega)
  have hfloor : (∑ d ∈ Finset.Icc 1 U, (Sawtooth.chi4 d : ℝ) * (⌊X / d⌋ : ℤ)) =
      X * betaSum U -
        (∑ d ∈ Finset.Icc 1 U, (Sawtooth.chi4 d : ℝ) * Sawtooth.psi (X / d)) -
        (Sawtooth.partialSum U : ℝ) / 2 := by
    rw [partialSum_eq_sum_Icc]
    unfold betaSum
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Sawtooth.floor_eq]
    ring
  have hpartial : (∑ m ∈ Finset.Icc 1 U, (Sawtooth.partialSum ⌊X / m⌋₊ : ℝ)) =
      U / 2 + (∑ m ∈ Finset.Icc 1 U,
        (Sawtooth.psi (X / (4 * m) + 1 / 4) - Sawtooth.psi (X / (4 * m) + 3 / 4))) := by
    calc
      _ = ∑ m ∈ Finset.Icc 1 U,
          (1 / 2 + (Sawtooth.psi (X / (4 * m) + 1 / 4) -
            Sawtooth.psi (X / (4 * m) + 3 / 4))) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [partialSum_floor_eq_floorDifference _ (by positivity), Sawtooth.floorDifference_sawtooth]
        have heq : X / (m : ℝ) / 4 = X / (4 * m) := by ring
        rw [heq]
        ring
      _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
  unfold circleError
  rw [circleCount_hyperbola h2 X U hU hlo hhi, hfloor, hpartial]
  unfold circleSawtooth betaB
  field_simp
  ring

/-- Section 7.3, equation (7.9), with the explicit uniform bound 23.
The only inputs are the classical coefficient identity and the ordered value β(1)=π/4;
the tail expansion, all shifts, the origin, and the endpoint cancellation are proved here. -/
theorem circleError_sawtooth (h2 : ClassicalInputs.TwoSquaresIdentity)
    (hβ : ClassicalInputs.BetaAtOne) (X : ℝ) (hX : 1 ≤ X) :
    |circleError X - circleSawtooth X ⌊Real.sqrt X⌋₊| ≤ 23 := by
  let U := ⌊Real.sqrt X⌋₊
  obtain ⟨hU, hlo, hhi⟩ := floor_sqrt_conditions X hX
  change 1 ≤ U at hU
  change (U : ℝ) ^ 2 ≤ X at hlo
  change X < (U + 1 : ℕ) ^ 2 at hhi
  have hUreal : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hUpos : (0 : ℝ) < U := by linarith
  have hU2 : 0 < (U : ℝ) ^ 2 := sq_pos_of_pos hUpos
  have hXpos : 0 < X := by linarith
  have hhi' : X < ((U : ℝ) + 1) ^ 2 := by exact_mod_cast hhi
  have hratio : X / (U : ℝ) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ hU2]
    nlinarith
  have hA : 0 ≤ (Sawtooth.partialSum U : ℝ) ∧ (Sawtooth.partialSum U : ℝ) ≤ 1 := by
    rcases Sawtooth.partialSum_zero_or_one U with hh | hh <;> simp [hh]
  have hconstant : |1 - 2 * (Sawtooth.partialSum U : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hlinear : |4 * (-(X / U) * betaB U + U * betaB U)| ≤ 6 := by
    have hh := Sawtooth.circle_linear_cancellation_bound hUreal hlo hhi' hA.1 hA.2
    unfold betaB
    rw [abs_mul]
    norm_num
    simp only [neg_mul] at hh
    linarith
  have htail : |4 * X * (Real.pi / 4 - betaSum U - betaB U / U)| ≤ 16 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * X)]
    calc
      _ ≤ 4 * X * (1 / (U : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (beta_tail_bound hβ U hU) (by positivity)
      _ = 4 * (X / (U : ℝ) ^ 2) := by ring
      _ ≤ 16 := by linarith
  rw [circleError_sawtooth_exact h2 X U hU hlo hhi]
  change |circleSawtooth X U + _ - circleSawtooth X U| ≤ 23
  rw [add_sub_cancel_left]
  calc
    _ ≤ |1 - 2 * (Sawtooth.partialSum U : ℝ)| +
        |4 * (-(X / U) * betaB U + U * betaB U)| +
        |4 * X * (Real.pi / 4 - betaSum U - betaB U / U)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 23 := by linarith

end
end CircleDivisor.DiscrepancyReduction
