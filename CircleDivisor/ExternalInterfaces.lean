import CircleDivisor.Statements

/-!
# Source-level arithmetic interface, with explicit numerical hypotheses

`LiYangInput` is an external theorem **statement**, not an axiom and not a
proved result. It records the fixed-q, weighted large-sieve/block-construction
input of Li--Yang, arXiv:2308.14859v2, Lemma 4.4 and (4.1)--(4.5), (4.8),
(4.12)--(4.14). Bounds are expressed by a universal majorant, avoiding the
undefined supremum of an unbounded set of real numbers.

The Fourier-analytic wave-envelope theorem is not represented by a vacuous
abstract `Prop` field in this file. Its remaining precise definitions are
listed in `EXTERNAL_INTERFACE_AUDIT_ROUND2.md`.
-/

namespace CircleDivisor.ExternalInterfaces
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- Actual bounded variation and supremum control on the source interval.
The resulting usual BV norm is at most `2 * W`. -/
structure BVControl (W : ℝ) (w : ℝ → ℂ) : Prop where
  norm_le : ∀ x ∈ Set.Icc (1 : ℝ) 2, ‖w x‖ ≤ W
  variation_le : eVariationOn w (Set.Icc (1 : ℝ) 2) ≤ ENNReal.ofReal W

theorem BVControl.boundedVariation {W : ℝ} {w : ℝ → ℂ} (h : BVControl W w) :
    BoundedVariationOn w (Set.Icc (1 : ℝ) 2) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.variation_le

/-- Endpoint derivatives are derivatives within the closed source interval;
outside values of a phase do not alter these hypotheses. -/
def phaseDerivative (j : ℕ) (F : ℝ → ℝ) : ℝ → ℝ :=
  iteratedDerivWithin j F (Set.Icc 1 2)

structure PhaseControl (c C : ℝ) (F : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 3 F (Set.Icc 1 2)
  derivatives : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ x ∈ Set.Icc (1 : ℝ) 2,
    c ≤ |phaseDerivative j F x| ∧ |phaseDerivative j F x| ≤ C
  curvature : ∀ x ∈ Set.Icc (1 : ℝ) 2,
    c ≤ |phaseDerivative 1 F x * phaseDerivative 3 F x -
      3 * (phaseDerivative 2 F x) ^ 2|

/-- The smaller-box moment on the manuscript's complete periods. -/
def etaBox (K L η : ℝ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => if i = 2 then
    Set.Icc (-(η * L * Real.sqrt K)⁻¹) ((η * L * Real.sqrt K)⁻¹)
    else Set.Icc 0 1)

def etaMoment (K L η q : ℝ) (a : ℤ → ℤ → ℂ) : ℝ :=
  (η * L * Real.sqrt K / 2) * ∫ x in etaBox K L η, ‖coneSum K L a x‖ ^ q

/-- Li--Yang (3.1) uses two periods in each of the integer coordinates.
Its equality with `etaMoment` is proved internally in `ExternalPeriodBridge`. -/
def etaSourceBox (K L η : ℝ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => if i = 2 then
    Set.Icc (-(η * L * Real.sqrt K)⁻¹) ((η * L * Real.sqrt K)⁻¹)
    else Set.Icc (-1) 1)

def etaSourceMoment (K L η q : ℝ) (a : ℤ → ℤ → ℂ) : ℝ :=
  (η * L * Real.sqrt K / 8) *
    ∫ x in etaSourceBox K L η, ‖coneSum K L a x‖ ^ q

theorem etaMoment_nonneg {K L η q : ℝ} (_hK : 0 ≤ K) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (a : ℤ → ℤ → ℂ) : 0 ≤ etaMoment K L η q a := by
  unfold etaMoment
  positivity

theorem etaSourceMoment_nonneg {K L η q : ℝ} (_hK : 0 ≤ K) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (a : ℤ → ℤ → ℂ) : 0 ≤ etaSourceMoment K L η q a := by
  unfold etaSourceMoment
  positivity

theorem coneSum_continuous (K L : ℝ) (a : ℤ → ℤ → ℂ) :
    Continuous (coneSum K L a) := by
  unfold coneSum exponential
  fun_prop

theorem exponential_add (x y : ℝ) : exponential (x + y) = exponential x * exponential y := by
  simp only [exponential, Complex.ofReal_add, mul_add, add_mul, Complex.exp_add]

theorem exponential_norm (x : ℝ) : ‖exponential x‖ = 1 := by
  simp [exponential, Complex.norm_exp]

theorem exponential_int (n : ℤ) : exponential n = 1 := by
  change Complex.exp ((2 : ℂ) * Real.pi * (n : ℂ) * Complex.I) = 1
  rw [show (2 : ℂ) * Real.pi * (n : ℂ) * Complex.I =
    (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

def translatedCoefficients (t : ℝ) (a : ℤ → ℤ → ℂ) (k l : ℤ) : ℂ :=
  a k l * exponential ((l : ℝ) * Real.sqrt k * t)

theorem translatedCoefficients_norm (t : ℝ) (a : ℤ → ℤ → ℂ) (k l : ℤ) :
    ‖translatedCoefficients t a k l‖ = ‖a k l‖ := by
  simp [translatedCoefficients, exponential_norm]

/-- Actual coefficient translation, used when covering the eta interval by
translates; no regularity of the coefficient array is required. -/
theorem coneSum_translate_third (K L t : ℝ) (a : ℤ → ℤ → ℂ) (x : Fin 3 → ℝ) :
    coneSum K L a (fun i => if i = 2 then x i + t else x i) =
      coneSum K L (translatedCoefficients t a) x := by
  unfold coneSum
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    if_false, if_true]
  rw [show (l : ℝ) * x 0 + k * l * x 1 + l * Real.sqrt k * (x 2 + t) =
      ((l : ℝ) * x 0 + k * l * x 1 + l * Real.sqrt k * x 2) +
        l * Real.sqrt k * t by ring,
    exponential_add]
  unfold translatedCoefficients
  ring

/-- Both integer-frequency coordinates really are periodic. This is the
pointwise part of converting the source's two periods to the manuscript's one. -/
theorem coneSum_integer_periods (K L : ℝ) (a : ℤ → ℤ → ℂ) (u v : ℤ)
    (x : Fin 3 → ℝ) :
    coneSum K L a (fun i => if i = 0 then x i + u else if i = 1 then x i + v else x i) =
      coneSum K L a x := by
  unfold coneSum
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_true, if_false]
  rw [show (l : ℝ) * (x 0 + u) + k * l * (x 1 + v) + l * Real.sqrt k * x 2 =
      ((l : ℝ) * x 0 + k * l * x 1 + l * Real.sqrt k * x 2) +
        ((l * u + k * l * v : ℤ) : ℝ) by push_cast; ring,
    exponential_add, exponential_int, mul_one]

theorem coneMoment_integrableOn (K L q : ℝ) (hq : 0 ≤ q)
    (a : ℤ → ℤ → ℂ) :
    IntegrableOn (fun x => ‖coneSum K L a x‖ ^ q) (momentBox K) := by
  have hc := (Real.continuous_rpow_const hq).comp (coneSum_continuous K L a).norm
  apply hc.continuousOn.integrableOn_compact
  unfold momentBox
  apply isCompact_univ_pi
  intro i
  split_ifs <;> exact isCompact_Icc

theorem eta_height_le {K L η : ℝ} (hK : 0 < K) (hL : 0 < L) (hη : 0 < η)
    (h : 1 ≤ η * K * L) : (η * L * Real.sqrt K)⁻¹ ≤ Real.sqrt K := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (mul_pos (mul_pos hη hL) hs)).2
  have he : Real.sqrt K * (η * L * Real.sqrt K) = η * K * L := by
    nlinarith [Real.sq_sqrt hK.le]
  rwa [he]

theorem etaBox_subset {K L η : ℝ} (hK : 0 < K) (hL : 0 < L) (hη : 0 < η)
    (h : 1 ≤ η * K * L) : etaBox K L η ⊆ momentBox K := by
  have he := eta_height_le hK hL hη h
  intro x hx i hi
  have hx' := hx i hi
  dsimp [etaBox] at hx'
  dsimp [momentBox]
  split_ifs with hi2
  · subst i
    simp only [if_true, Set.mem_Icc] at hx'
    exact ⟨by linarith [hx'.1], le_trans hx'.2 he⟩
  · simpa [hi2] using hx'

/-- The exact internal integral comparison behind manuscript (5.10), for
ordered boxes. This is not an external spacing estimate. -/
theorem etaMoment_le {K L η q : ℝ} (hK : 0 < K) (hL : 0 < L) (hη : 0 < η)
    (hq : 0 ≤ q) (h : 1 ≤ η * K * L) (a : ℤ → ℤ → ℂ) :
    etaMoment K L η q a ≤ (η * K * L) * coneMoment K L q a := by
  have hint := setIntegral_mono_set (coneMoment_integrableOn K L q hq a)
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (Filter.Eventually.of_forall (etaBox_subset hK hL hη h))
  have hs : Real.sqrt K ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hK)
  have hc : η * L * Real.sqrt K / 2 = η * K * L * (2 * Real.sqrt K)⁻¹ := by
    field_simp
    nlinarith [Real.sq_sqrt hK.le]
  unfold etaMoment coneMoment
  rw [← mul_assoc, ← hc]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

/-- Comparability has a single fixed constant, quantified before all scales. -/
def Comparable (D x y : ℝ) : Prop := y / D ≤ x ∧ x ≤ D * y

inductive BlockCase where
  | A
  | B
  deriving DecidableEq

def caseA (H M T : ℝ) : Prop :=
  M ^ (-9 : ℝ) * T ^ (4 : ℝ) * (Real.log T) ^ ((171 : ℝ) / 140) ≤ H ∧
    H ≤ M * T ^ (-(49 : ℝ) / 164)

def caseB (B₀ H M T : ℝ) : Prop :=
  H ≤ min (M ^ ((35 : ℝ) / 69) * T ^ (-(2 : ℝ) / 23))
    (B₀ * M ^ ((3 : ℝ) / 2) * T ^ (-(1 : ℝ) / 2))

def admissibleCase (b : BlockCase) (B₀ H M T : ℝ) : Prop :=
  match b with
  | .A => caseA H M T
  | .B => caseB B₀ H M T

def blockLengthA (H M T : ℝ) : ℝ :=
  M ^ ((41 : ℝ) / 25) * H ^ (-(16 : ℝ) / 25) * T ^ (-(49 : ℝ) / 100) *
    (Real.log T) ^ ((969 : ℝ) / 14000)

def blockLengthB (H M T : ℝ) : ℝ :=
  min (M ^ ((7 : ℝ) / 8) * H ^ (-(29 : ℝ) / 40) * T ^ (-(3 : ℝ) / 20) *
    (Real.log T) ^ ((969 : ℝ) / 5600))
    (M ^ (2 : ℝ) * H ^ (-(1 : ℝ) / 3) * T ^ (-(2 : ℝ) / 3))

def blockLength (b : BlockCase) (H M T : ℝ) : ℝ :=
  match b with
  | .A => blockLengthA H M T
  | .B => blockLengthB H M T

def denominatorCutoff (H R : ℝ) : ℝ :=
  R * (H / R) ^ ((39 : ℝ) / 119) * (Real.log (2 * H / R)) ^ (-(3 : ℝ) / 4)

/-- The source has a further upper cutoff `3H`, as well as `Q ≲ Q₂`. -/
def denominatorAdmissible (D H R Q : ℝ) : Prop :=
  R ≤ Q ∧ Q ≤ 3 * H ∧ Q ≤ D * denominatorCutoff H R

/-- Source integer K,L, positive eta, exact order restrictions and fixed
comparison factors. None is a free, uninterpreted analytic hypothesis. -/
structure SpacingParameters (D H N R Q : ℝ) (K L : ℕ) (η : ℝ) : Prop where
  L_one : 1 ≤ L
  L_le_K : L ≤ K
  eta_pos : 0 < η
  K_le_eta_inv : (K : ℝ) ≤ η⁻¹
  eta_inv_le_KL : η⁻¹ ≤ (K : ℝ) * L
  K_comparable : Comparable D K (N * Q / R ^ 2)
  L_comparable : Comparable D L (H * Q / R ^ 2)
  eta_comparable : Comparable D η (R ^ 2 / (N * H))
  eta_product_comparable : Comparable D (η * K * L) ((Q / R) ^ 2)

theorem SpacingParameters.one_le_eta_product {D H N R Q η : ℝ} {K L : ℕ}
    (p : SpacingParameters D H N R Q K L η) : 1 ≤ η * K * L := by
  have h := mul_le_mul_of_nonneg_left p.eta_inv_le_KL p.eta_pos.le
  simpa [ne_of_gt p.eta_pos, mul_assoc] using h

theorem etaMoment_le_of_spacingParameters {D H N R Q η q : ℝ} {K L : ℕ}
    (p : SpacingParameters D H N R Q K L η) (hq : 0 ≤ q) (a : ℤ → ℤ → ℂ) :
    etaMoment K L η q a ≤ (η * K * L) * coneMoment K L q a := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.L_one)
  have hK : 0 < (K : ℝ) := lt_of_lt_of_le hL (by exact_mod_cast p.L_le_K)
  exact etaMoment_le hK hL p.eta_pos hq p.one_le_eta_product a

def sieveFactor (H M N R Q q : ℝ) : ℝ :=
  (R / Q) ^ (3 - 6 / q) * (M * R / N) * (H / R) ^ (22 / (17 * q))

/-- An upper bound for every actual spacing norm in the source maximum.
Requiring every admissible parameter choice safely enlarges its index set. -/
def spacingMajorized (D H M N R q B : ℝ) : Prop :=
  ∀ Q : ℝ, denominatorAdmissible D H R Q →
    ∀ K L : ℕ, ∀ η : ℝ, SpacingParameters D H N R Q K L η →
      ∀ a : ℤ → ℤ → ℂ, (∀ k l, ‖a k l‖ ≤ 1) →
        sieveFactor H M N R Q q * (etaSourceMoment K L η q a) ^ (1 / q) ≤ B

/-- Required source geometry, to be verified internally in the hard range.
Remark 4.5 explicitly warns that `R <= H` does not follow from the cases. -/
structure BlockSeparation (D C H M N R : ℝ) : Prop where
  R_large : D ≤ R
  R_small : D * R ≤ H
  H_small : 64 * C * H ≤ N
  N_small : D * N ≤ M

/-- Once uniform positive margins have been established, absorbing the fixed
source constants reduces to these four ordinary real inequalities. -/
theorem blockSeparation_of_margin {D C H M N R A : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hN : 0 ≤ N) (hDA : D ≤ A)
    (hCA : 64 * C ≤ A) (hAR : A ≤ R)
    (hRH : A * R ≤ H) (hHN : A * H ≤ N) (hNM : A * N ≤ M) :
    BlockSeparation D C H M N R := by
  refine ⟨le_trans hDA hAR, ?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right hDA hR) hRH
  · exact le_trans (mul_le_mul_of_nonneg_right hCA hH) hHN
  · exact le_trans (mul_le_mul_of_nonneg_right hDA hN) hNM

/-- Fixed-q Li--Yang input for the range needed in this manuscript.

The parameter C is at least the original C_2 and also at least 1/c. The
separation premise retains (4.13) and Remark 4.5. In particular the statement
does not promise `R <= H` from Case A/B alone. Fixed factors and thresholds
precede F, weights, H,M,T. The phase may have an arbitrarily large additive
constant. No first-spacing bound, (4.6), or main theorem is assumed here.

The half-open sum convention is the specialization to endpoint indicator
weights of the closed/partial-rectangle formulation in the source.
-/
def LiYangInput : Prop :=
  ∀ q : ℝ, 4 < q → q ≤ 9 / 2 →
    ∀ c C W ε : ℝ, 0 < c → 2 ≤ C → 1 / c ≤ C → 0 < W → 0 < ε →
      ∃ B₀ D M₀ T₀ A : ℝ,
        0 < B₀ ∧ 1 ≤ D ∧ 1 ≤ M₀ ∧ 2 ≤ T₀ ∧ 0 < A ∧
        ∀ F : ℝ → ℝ, PhaseControl c C F →
        ∀ g G : ℝ → ℂ, BVControl W g → BVControl W G →
        ∀ H M T : ℝ, 1 ≤ H → M₀ ≤ M → T₀ ≤ T → M ≤ Real.sqrt T →
        ∀ b : BlockCase, admissibleCase b B₀ H M T →
          ∃ N : ℕ, ∃ R : ℝ,
            0 < N ∧ 0 < R ∧
            Comparable D N (blockLength b H M T) ∧
            Comparable D (R ^ 2) (M ^ 3 / (N * T)) ∧
            (BlockSeparation D C H M N R →
            (∃ Q : ℝ, denominatorAdmissible D H R Q ∧
              ∃ K L : ℕ, ∃ η : ℝ, SpacingParameters D H N R Q K L η) ∧
            ∀ B : ℝ, 0 ≤ B → spacingMajorized D H M N R q B →
              ‖reciprocalSum H M T F g G‖ ≤ A * T ^ ε * B)

/-- The q quantifier remains outside all constants: this is intentionally not
an unproved exchange of `forall q, exists A` and `exists A, forall q`. -/
theorem liYang_fixed_q (input : LiYangInput) (q : ℝ) (hq : 4 < q)
    (hqu : q ≤ 9 / 2) :
    ∀ c C W ε : ℝ, 0 < c → 2 ≤ C → 1 / c ≤ C → 0 < W → 0 < ε →
      ∃ B₀ D M₀ T₀ A : ℝ,
        0 < B₀ ∧ 1 ≤ D ∧ 1 ≤ M₀ ∧ 2 ≤ T₀ ∧ 0 < A ∧
        ∀ F : ℝ → ℝ, PhaseControl c C F →
        ∀ g G : ℝ → ℂ, BVControl W g → BVControl W G →
        ∀ H M T : ℝ, 1 ≤ H → M₀ ≤ M → T₀ ≤ T → M ≤ Real.sqrt T →
        ∀ b : BlockCase, admissibleCase b B₀ H M T →
          ∃ N : ℕ, ∃ R : ℝ,
            0 < N ∧ 0 < R ∧
            Comparable D N (blockLength b H M T) ∧
            Comparable D (R ^ 2) (M ^ 3 / (N * T)) ∧
            (BlockSeparation D C H M N R →
            (∃ Q : ℝ, denominatorAdmissible D H R Q ∧
              ∃ K L : ℕ, ∃ η : ℝ, SpacingParameters D H N R Q K L η) ∧
            ∀ B : ℝ, 0 ≤ B → spacingMajorized D H M N R q B →
              ‖reciprocalSum H M T F g G‖ ≤ A * T ^ ε * B) :=
  input q hq hqu

end
end CircleDivisor.ExternalInterfaces
