import CircleDivisor.GuthMaldagueInput
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! Uniform derivative estimates for rational envelope factors. These estimates
are internal proofs for the explicit polynomially decaying weight. -/

namespace CircleDivisor.EnergyV3.KernelDerivatives
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option maxHeartbeats 1200000

def inversePower (z : ℂ) : ℂ := z ^ (-100 : ℤ)

def inversePowerCoefficient (n : ℕ) : ℝ :=
  ‖∏ i ∈ Finset.range n, ((-100 : ℂ) - i)‖

theorem inversePower_smooth_at (z : ℂ) (hz : z ≠ 0) :
    ContDiffAt ℂ ∞ inversePower z := by
  have hf : ContDiffAt ℂ ∞ (fun z : ℂ => (z ^ 100)⁻¹) z :=
    (contDiffAt_id.pow 100).inv (pow_ne_zero _ hz)
  convert hf using 1
  ext w
  unfold inversePower
  rw [show (-100 : ℤ) = -(100 : ℕ) by norm_num, zpow_neg, zpow_natCast]

theorem inversePower_complex_derivative (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℂ n inversePower z‖ =
      inversePowerCoefficient n * ‖z‖ ^ (-100 - (n : ℤ)) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  unfold inversePower
  rw [iteratedDeriv_eq_iterate, iter_deriv_zpow, norm_mul, norm_zpow]
  norm_num [inversePowerCoefficient]

theorem inversePower_real_derivative_bound (n : ℕ) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖iteratedFDeriv ℝ n inversePower z‖ ≤
      inversePowerCoefficient n * ‖z‖ ^ (-100 : ℤ) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz; norm_num at hz
  have hs : ContDiffAt ℂ n inversePower z := (inversePower_smooth_at z hz0).of_le
    (by exact_mod_cast le_top)
  rw [← hs.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  rw [inversePower_complex_derivative]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply zpow_le_zpow_right₀ hz
  omega

theorem affine_derivative_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (c : ℂ) (hL : ‖L‖ ≤ 1) (i : ℕ) (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => L y + c) x‖ ≤ 1 := by
  have hd : fderiv ℝ (fun y => L y + c) = fun _ => L := by
    ext y
    rw [fderiv_add_const, L.fderiv]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_comm, ← norm_iteratedFDeriv_fderiv, hd]
  by_cases hj : j = 0
  · subst j
    simpa only [norm_iteratedFDeriv_zero] using hL
  · rw [iteratedFDeriv_const_of_ne hj]
    norm_num

def atomDerivativeConstant (n : ℕ) : ℝ :=
  n.factorial * ∑ i ∈ Finset.range (n + 1), inversePowerCoefficient i

/-- Every derivative of a rational atom retains its full original decay.
The constant is independent of the continuous linear coordinate and the shift. -/
theorem inversePower_affine_derivative_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (c : ℂ) (hL : ‖L‖ ≤ 1)
    (haway : ∀ x : E, 1 ≤ ‖L x + c‖) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => inversePower (L y + c)) x‖ ≤
      atomDerivativeConstant n * ‖L x + c‖ ^ (-100 : ℤ) := by
  let s : Set ℂ := {z | z ≠ 0}
  have hopen : IsOpen s := isOpen_ne
  have hne (y : E) : L y + c ≠ 0 := by
    intro h
    have hh := haway y
    rw [h, norm_zero] at hh
    norm_num at hh
  have hg : ContDiffOn ℝ ∞ inversePower s := by
    intro z hz
    exact ((inversePower_smooth_at z hz).restrict_scalars ℝ).contDiffWithinAt
  have hf : ContDiff ℝ ∞ (fun y : E => L y + c) := L.contDiff.add contDiff_const
  have hmajorant : ∀ i ≤ n,
      ‖iteratedFDerivWithin ℝ i inversePower s (L x + c)‖ ≤
        (∑ j ∈ Finset.range (n + 1), inversePowerCoefficient j) *
          ‖L x + c‖ ^ (-100 : ℤ) := by
    intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn
      (((inversePower_smooth_at _ (hne x)).restrict_scalars ℝ).of_le (by exact_mod_cast le_top))
      (hne x)]
    apply (inversePower_real_derivative_bound i _ (haway x)).trans
    apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (norm_nonneg _) _)
    exact Finset.single_le_sum (a := i) (s := Finset.range (n + 1))
      (f := inversePowerCoefficient) (fun j hj => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hh := norm_iteratedFDeriv_comp_le'
    (g := inversePower) (f := fun y : E => L y + c)
    (fun z hz => by obtain ⟨y, rfl⟩ := hz; exact hne y)
    hopen.uniqueDiffOn hg hf (n := n) (by exact_mod_cast le_top) x hmajorant
    (D := 1) (fun i hi hi' => by simpa using affine_derivative_bound L c hL i hi x)
  simpa only [Function.comp_def, one_pow, mul_one, atomDerivativeConstant, mul_assoc] using hh

open GuthMaldague

def coordinateComplex (k : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj k)

theorem coordinateComplex_apply (k : Fin 3) (u : Space) : coordinateComplex k u = (u k : ℂ) := rfl

theorem coordinateComplex_norm (k : Fin 3) : ‖coordinateComplex k‖ ≤ 1 := by
  apply (coordinateComplex k).opNorm_le_bound (by norm_num)
  intro u
  simp only [coordinateComplex_apply, Complex.norm_real, one_mul]
  exact PiLp.norm_apply_le u k

theorem real_add_I_away (x : ℝ) : 1 ≤ ‖(x : ℂ) + Complex.I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) + Complex.I)

theorem real_sub_I_away (x : ℝ) : 1 ≤ ‖(x : ℂ) - Complex.I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) - Complex.I)

theorem inversePower_pair (x : ℝ) :
    inversePower ((x : ℂ) + Complex.I) * inversePower ((x : ℂ) - Complex.I) =
      (((1 + x ^ 2) ^ 100)⁻¹ : ℝ) := by
  unfold inversePower
  rw [← mul_zpow]
  have heq : ((x : ℂ) + Complex.I) * ((x : ℂ) - Complex.I) = (1 + x ^ 2 : ℝ) := by
    push_cast
    calc
      _ = (x : ℂ) ^ 2 - Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [heq, show (-100 : ℤ) = -(100 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  push_cast
  rfl

theorem inversePower_norm_pair (x : ℝ) :
    ‖(x : ℂ) + Complex.I‖ ^ (-100 : ℤ) * ‖(x : ℂ) - Complex.I‖ ^ (-100 : ℤ) =
      ((1 + x ^ 2) ^ 100)⁻¹ := by
  rw [← norm_zpow, ← norm_zpow, ← norm_mul]
  change ‖inversePower ((x : ℂ) + Complex.I) * inversePower ((x : ℂ) - Complex.I)‖ = _
  rw [inversePower_pair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

def weightCoordinate (k : Fin 3) (u : Space) : ℂ := (((1 + (u k) ^ 2) ^ 100)⁻¹ : ℝ)

theorem weightCoordinate_smooth (k : Fin 3) : ContDiff ℝ ∞ (weightCoordinate k) := by
  have hcoord : ContDiff ℝ ∞ (fun u : Space => u k) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff
  have hbase : ContDiff ℝ ∞ (fun u : Space => 1 + (u k) ^ 2) :=
    contDiff_const.add (hcoord.pow 2)
  have hpower : ContDiff ℝ ∞ (fun u : Space => (1 + (u k) ^ 2) ^ 100) := hbase.pow 100
  have hh : ContDiff ℝ ∞ (fun u : Space => ((1 + (u k) ^ 2) ^ 100)⁻¹) :=
    hpower.inv (fun u => by positivity)
  exact Complex.ofRealCLM.contDiff.comp hh

def coordinateDerivativeConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * atomDerivativeConstant i * atomDerivativeConstant (n - i)

theorem atomDerivativeConstant_nonneg (n : ℕ) : 0 ≤ atomDerivativeConstant n := by
  unfold atomDerivativeConstant inversePowerCoefficient
  positivity

theorem coordinateDerivativeConstant_nonneg (n : ℕ) : 0 ≤ coordinateDerivativeConstant n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (atomDerivativeConstant_nonneg _))
    (atomDerivativeConstant_nonneg _)

theorem weightCoordinate_derivative_bound (k : Fin 3) (n : ℕ) (u : Space) :
    ‖iteratedFDeriv ℝ n (weightCoordinate k) u‖ ≤
      coordinateDerivativeConstant n * ((1 + (u k) ^ 2) ^ 100)⁻¹ := by
  let p : Space → ℂ := fun y => inversePower ((y k : ℂ) + Complex.I)
  let m : Space → ℂ := fun y => inversePower ((y k : ℂ) - Complex.I)
  have hp : ContDiff ℝ ∞ p := by
    rw [contDiff_iff_contDiffAt]
    intro y
    apply ((inversePower_smooth_at _ (by
      have hh := real_add_I_away (y k)
      intro h
      rw [h, norm_zero] at hh
      norm_num at hh)).restrict_scalars ℝ).comp y
    exact ((coordinateComplex k).contDiff.contDiffAt.add contDiffAt_const)
  have hm : ContDiff ℝ ∞ m := by
    rw [contDiff_iff_contDiffAt]
    intro y
    apply ((inversePower_smooth_at _ (by
      have hh := real_sub_I_away (y k)
      intro h
      rw [h, norm_zero] at hh
      norm_num at hh)).restrict_scalars ℝ).comp y
    exact ((coordinateComplex k).contDiff.contDiffAt.sub contDiffAt_const)
  have heq : weightCoordinate k = fun y => p y * m y := by
    ext y
    exact (inversePower_pair (y k)).symm
  rw [heq]
  apply (norm_iteratedFDeriv_mul_le hp hm u (n := n) (by exact_mod_cast le_top)).trans
  have hpbound (i : ℕ) : ‖iteratedFDeriv ℝ i p u‖ ≤
      atomDerivativeConstant i * ‖(u k : ℂ) + Complex.I‖ ^ (-100 : ℤ) :=
    inversePower_affine_derivative_bound (coordinateComplex k) Complex.I (coordinateComplex_norm k)
      (fun y => real_add_I_away (y k)) i u
  have hmbound (i : ℕ) : ‖iteratedFDeriv ℝ i m u‖ ≤
      atomDerivativeConstant i * ‖(u k : ℂ) - Complex.I‖ ^ (-100 : ℤ) := by
    simpa only [← sub_eq_add_neg, coordinateComplex_apply, m] using
      inversePower_affine_derivative_bound (coordinateComplex k) (-Complex.I) (coordinateComplex_norm k)
        (fun y => real_sub_I_away (y k)) i u
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (atomDerivativeConstant i * ‖(u k : ℂ) + Complex.I‖ ^ (-100 : ℤ)) *
          (atomDerivativeConstant (n - i) * ‖(u k : ℂ) - Complex.I‖ ^ (-100 : ℤ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hpbound i) (Nat.cast_nonneg _)
      · exact hmbound (n - i)
      · positivity
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (atomDerivativeConstant_nonneg _) (by positivity))
    _ = coordinateDerivativeConstant n * ((1 + (u k) ^ 2) ^ 100)⁻¹ := by
      unfold coordinateDerivativeConstant
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← inversePower_norm_pair (u k)]
      ring

def baseDerivativeConstant (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym n,
    ((p : Multiset (Fin 3)).countPerms : ℝ) *
      ∏ k : Fin 3, coordinateDerivativeConstant ((p : Multiset (Fin 3)).count k)

theorem baseDerivativeConstant_nonneg (n : ℕ) : 0 ≤ baseDerivativeConstant n := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun k hk => coordinateDerivativeConstant_nonneg _))

theorem baseWeight_complex_eq : (fun u : Space => (baseWeight u : ℂ)) =
    fun u => ∏ k : Fin 3, weightCoordinate k u := by
  ext u
  simp [baseWeight, weightCoordinate]

theorem baseWeight_complex_smooth : ContDiff ℝ ∞ (fun u : Space => (baseWeight u : ℂ)) := by
  rw [baseWeight_complex_eq]
  exact contDiff_prod (fun k hk => weightCoordinate_smooth k)

/-- The full product weight has every derivative bounded by the same original
integrable weight, with a constant depending only on the derivative order. -/
theorem baseWeight_derivative_bound (n : ℕ) (u : Space) :
    ‖iteratedFDeriv ℝ n (fun y : Space => (baseWeight y : ℂ)) u‖ ≤
      baseDerivativeConstant n * baseWeight u := by
  rw [baseWeight_complex_eq]
  apply (norm_iteratedFDeriv_prod_le (fun k hk => weightCoordinate_smooth k)
    (n := n) (x := u) (by exact_mod_cast le_top)).trans
  calc
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym n,
        ((p : Multiset (Fin 3)).countPerms : ℝ) *
          ∏ k : Fin 3, coordinateDerivativeConstant ((p : Multiset (Fin 3)).count k) *
            ((1 + (u k) ^ 2) ^ 100)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.prod_le_prod (fun k hk => norm_nonneg _)
      intro k hk
      exact weightCoordinate_derivative_bound k _ u
    _ = baseDerivativeConstant n * baseWeight u := by
      simp only [Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul,
        baseDerivativeConstant, baseWeight]

end
end CircleDivisor.EnergyV3.KernelDerivatives
