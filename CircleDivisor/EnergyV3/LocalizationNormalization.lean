import CircleDivisor.ExternalPeriodBridge
import CircleDivisor.EnergyV3.LinearTransport
import CircleDivisor.EnergyV3.PairedCountReal
import CircleDivisor.ConeGeometry

namespace CircleDivisor.EnergyV3.LocalizationNormalization
open MeasureTheory Finset
open scoped Matrix RealInnerProductSpace ENNReal
noncomputable section
abbrev Space := FourierLocalization.Space
abbrev PiSpace := Fin 3 → ℝ

theorem periodic_nat_periods {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (n : ℕ) :
    (∫ t in Set.Icc (0 : ℝ) n, f t) = n * ∫ t in Set.Icc (0 : ℝ) 1, f t := by
  have h := hp.intervalIntegral_add_zsmul_eq (n : ℤ) 0 (fun a b => hf.intervalIntegrable a b)
  simpa only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one, intervalIntegral.integral_of_le (Nat.cast_nonneg n),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_Icc_eq_integral_Ioc] using h

def enlargedBox (K : ℝ) : Set PiSpace :=
  Set.pi Set.univ ![Set.Icc 0 (Nat.ceil K : ℝ), Set.Icc (0:ℝ) 1, Set.Icc (-Real.sqrt K) (Real.sqrt K)]

theorem integral_enlargedBox (K L q : ℝ) (hq : 0 ≤ q) (a : ℤ → ℤ → ℂ) :
    (∫ x in enlargedBox K, ‖coneSum K L a x‖ ^ q) =
      (Nat.ceil K : ℝ) * ∫ x in momentBox K, ‖coneSum K L a x‖ ^ q := by
  let f : PiSpace → ℝ := fun x => ‖coneSum K L a x‖ ^ q
  let s : Fin 2 → Set ℝ := ![Set.Icc (0:ℝ) 1, Set.Icc (-Real.sqrt K) (Real.sqrt K)]
  let μ (b : ℝ) : Fin 3 → Measure ℝ := fun j => volume.restrict (((0 : Fin 3).insertNth (Set.Icc (0:ℝ) b) s : Fin 3 → Set ℝ) j)
  have hf : Continuous f := (Real.continuous_rpow_const hq).comp (ExternalInterfaces.coneSum_continuous K L a).norm
  have hi (b : ℝ) : Integrable f (Measure.pi (μ b)) := by
    rw [← Measure.restrict_pi_pi]
    apply hf.continuousOn.integrableOn_compact
    apply isCompact_univ_pi
    intro j
    fin_cases j <;> exact isCompact_Icc
  have hsource := ExternalPeriodBridge.integral_pi_insertNth (μ (Nat.ceil K)) (0 : Fin 3) f (hi _)
  have htarget := ExternalPeriodBridge.integral_pi_insertNth (μ 1) (0 : Fin 3) f (hi _)
  have he (b : ℝ) : (0 : Fin 3).insertNth (Set.Icc (0:ℝ) b) s =
      ![Set.Icc (0:ℝ) b, Set.Icc (0:ℝ) 1, Set.Icc (-Real.sqrt K) (Real.sqrt K)] := by ext j; fin_cases j <;> rfl
  have heM : momentBox K = Set.pi Set.univ ((0 : Fin 3).insertNth (Set.Icc (0:ℝ) 1) s) := by
    unfold momentBox
    congr 1
    ext j
    fin_cases j <;> simp [s, Fin.insertNth, Fin.succAboveCases]
  have heE : enlargedBox K = Set.pi Set.univ ((0 : Fin 3).insertNth (Set.Icc (0:ℝ) (Nat.ceil K : ℝ)) s) := by rw [he]; rfl
  rw [heM, heE]
  change (∫ x, f x ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict _) =
    (Nat.ceil K : ℝ) * (∫ x, f x ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict _)
  rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi, hsource, htarget]
  simp only [μ, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  apply periodic_nat_periods
  · exact hf.comp (by fun_prop)
  · exact ExternalPeriodBridge.moment_periodic_insertNth_zero K L q a y

def physicalLinear (K L : ℝ) : PiSpace →ₗ[ℝ] PiSpace where
  toFun x := ![L*x 0, L*Real.sqrt K*x 2, K*L*x 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

def physicalInverse (K L : ℝ) (z : PiSpace) : PiSpace :=
  ![z 0/L, z 2/(K*L), z 1/(L*Real.sqrt K)]

def physicalEquiv (K L : ℝ) (hK : 0 < K) (hL : 0 < L) : PiSpace ≃L[ℝ] PiSpace :=
  ({ physicalLinear K L with
      invFun := physicalInverse K L
      left_inv := by intro x; ext i; fin_cases i <;> simp [physicalInverse, physicalLinear, hK.ne', hL.ne', (Real.sqrt_pos.mpr hK).ne']
      right_inv := by intro x; ext i; fin_cases i <;> simp [physicalInverse, physicalLinear] <;> field_simp } : PiSpace ≃ₗ[ℝ] PiSpace).toContinuousLinearEquiv

def physicalMatrix (K L : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![L,0,0; 0,0,L*Real.sqrt K; 0,K*L,0]

theorem physicalMatrix_det (K L : ℝ) : (physicalMatrix K L).det = -K*L^3*Real.sqrt K := by
  simp [physicalMatrix, Matrix.det_fin_three]
  ring

theorem physicalMatrix_toLin (K L : ℝ) : Matrix.toLin' (physicalMatrix K L) = physicalLinear K L := by
  ext x i
  fin_cases i <;> simp [physicalMatrix, physicalLinear, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem physical_map (K L : ℝ) (hK : 0 < K) (hL : 0 < L) :
    Measure.map (physicalLinear K L) volume =
      ENNReal.ofReal (1/(K*L^3*Real.sqrt K)) • volume := by
  have hd : (physicalMatrix K L).det ≠ 0 := by
    rw [physicalMatrix_det]
    have hp : 0 < K*L^3*Real.sqrt K := by positivity
    nlinarith
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  rw [physicalMatrix_toLin, physicalMatrix_det] at hm
  convert hm using 2
  rw [show -K*L^3*Real.sqrt K = -(K*L^3*Real.sqrt K) by ring, inv_neg, abs_neg,
    abs_of_pos (by positivity : 0 < (K*L^3*Real.sqrt K)⁻¹), one_div]

theorem integral_physical_comp (K L : ℝ) (hK : 0 < K) (hL : 0 < L) (f : PiSpace → ℝ) :
    (∫ x, f (physicalLinear K L x)) = (1/(K*L^3*Real.sqrt K)) * ∫ z, f z := by
  have hh := (physicalEquiv K L hK hL).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) f
  change (∫ z, f z ∂Measure.map (physicalLinear K L) volume) = ∫ x, f (physicalLinear K L x) at hh
  rw [← hh, physical_map K L hK hL, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(K*L^3*Real.sqrt K)), smul_eq_mul]

theorem integrable_physical_comp (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (f : PiSpace → ℝ) (hf : Integrable f) : Integrable (fun x => f (physicalLinear K L x)) := by
  have hm : Integrable f (Measure.map (physicalLinear K L) volume) := by
    rw [physical_map K L hK hL]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_measurable (physicalLinear K L).continuous_of_finiteDimensional.measurable

def unlocalized (K L : ℝ) (a : ℤ → ℤ → ℂ) (z : Space) : ℂ :=
  ∑ k ∈ dyadicIntegers K, ∑ l ∈ dyadicIntegers L,
    a k l * FourierLocalization.character (FourierLocalization.coneFrequency K L k l) z

theorem character_physical (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (k l : ℤ) (x : PiSpace) :
    FourierLocalization.character (FourierLocalization.coneFrequency K L k l)
      (WithLp.toLp 2 (physicalLinear K L x)) =
      exponential ((l:ℝ)*x 0 + (k:ℝ)*l*x 1 + l*Real.sqrt k*x 2) := by
  simp [FourierLocalization.character, FourierLocalization.coneFrequency, physicalLinear,
    PiLp.inner_apply, Fin.sum_univ_succ, Real.fourierChar_apply, exponential]
  congr 1
  push_cast
  have hcK : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hcL : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hcS : (Real.sqrt K : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hK).ne'
  field_simp [hcK, hcL, hcS]
  ring

theorem unlocalized_physical (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (a : ℤ → ℤ → ℂ) (x : PiSpace) :
    unlocalized K L a (WithLp.toLp 2 (physicalLinear K L x)) = coneSum K L a x := by
  simp only [unlocalized, coneSum, character_physical K L hK hL]

theorem unlocalized_continuous (K L : ℝ) (a : ℤ → ℤ → ℂ) : Continuous (unlocalized K L a) := by
  apply continuous_finsetSum
  intro k hk
  apply continuous_finsetSum
  intro l hl
  exact continuous_const.mul (FourierLocalization.continuous_character _)

theorem unlocalized_norm_le (K L : ℝ) (a : ℤ → ℤ → ℂ) (z : Space) :
    ‖unlocalized K L a z‖ ≤ ∑ k ∈ dyadicIntegers K, ∑ l ∈ dyadicIntegers L, ‖a k l‖ := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k hk
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro l hl
  simp [norm_mul, FourierLocalization.character]

def localized (K L : ℝ) (χ : Space → ℂ) (a : ℤ → ℤ → ℂ) (z : Space) : ℂ :=
  FourierLocalization.dilate (K*L) χ z * unlocalized K L a z

theorem localized_continuous (K L : ℝ) (χ : SchwartzMap Space ℂ) (a : ℤ → ℤ → ℂ) :
    Continuous (localized K L χ a) :=
  (χ.continuous.comp (continuous_const_smul _)).mul (unlocalized_continuous K L a)

theorem localized_integrable_norm_rpow (K L q : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hq : 0 < q) (χ : SchwartzMap Space ℂ) (a : ℤ → ℤ → ℂ) :
    Integrable (fun z => ‖localized K L χ a z‖ ^ q) := by
  let B : ℝ := ∑ k ∈ dyadicIntegers K, ∑ l ∈ dyadicIntegers L, ‖a k l‖
  have hB : 0 ≤ B := sum_nonneg (fun k hk => sum_nonneg (fun l hl => norm_nonneg _))
  have hχq : Integrable (fun z => ‖χ z‖ ^ q) := by
    simpa only [ENNReal.toReal_ofReal hq.le] using
      (χ.memLp (ENNReal.ofReal q)).integrable_norm_rpow
        (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top
  have hd : Integrable (fun z => ‖FourierLocalization.dilate (K*L) χ z‖ ^ q) :=
    hχq.comp_smul (inv_ne_zero (mul_pos hK hL).ne')
  apply (hd.mul_const (B ^ q)).mono'
    (((Real.continuous_rpow_const hq.le).comp (localized_continuous K L χ a).norm).aestronglyMeasurable)
  filter_upwards with z
  change ‖‖localized K L χ a z‖ ^ q‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  dsimp [localized]
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) (unlocalized_norm_le K L a z) hq.le) (by positivity)

theorem normalized_physical_norm (K L : ℝ) (hK : 1 ≤ K) (hL : 0 < L)
    (x : PiSpace) (hx : x ∈ enlargedBox K) :
    ‖(K*L)⁻¹ • (WithLp.toLp 2 (physicalLinear K L x) : Space)‖ ≤ 3 := by
  have hKp : 0 < K := by linarith
  have hS : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKp
  have hx0 := hx (0 : Fin 3) (Set.mem_univ _)
  have hx1 := hx (1 : Fin 3) (Set.mem_univ _)
  have hx2 := hx (2 : Fin 3) (Set.mem_univ _)
  change 0 ≤ x 0 ∧ x 0 ≤ (Nat.ceil K : ℝ) at hx0
  change 0 ≤ x 1 ∧ x 1 ≤ 1 at hx1
  change -Real.sqrt K ≤ x 2 ∧ x 2 ≤ Real.sqrt K at hx2
  have hc := PairedCount.ceil_le_twice K hK
  have hy0 : 0 ≤ x 0/K ∧ x 0/K ≤ 2 := ⟨div_nonneg hx0.1 hKp.le, (div_le_iff₀ hKp).mpr (by linarith)⟩
  have hy2 : -(1:ℝ) ≤ x 2/Real.sqrt K ∧ x 2/Real.sqrt K ≤ 1 := by
    constructor
    · exact (le_div_iff₀ hS).mpr (by linarith [hx2.1])
    · exact (div_le_iff₀ hS).mpr (by linarith [hx2.2])
  have he : (K*L)⁻¹ • (WithLp.toLp 2 (physicalLinear K L x) : Space) =
      WithLp.toLp 2 ![x 0/K, x 2/Real.sqrt K, x 1] := by
    ext i
    fin_cases i <;> simp [physicalLinear] <;> field_simp
    nlinarith [Real.sq_sqrt hKp.le]
  rw [he]
  have hnorm := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 ![x 0/K, x 2/Real.sqrt K, x 1])
  simp [Fin.sum_univ_succ] at hnorm
  nlinarith [norm_nonneg (WithLp.toLp 2 ![x 0/K, x 2/Real.sqrt K, x 1])]

/-- Full Appendix A.1 normalization: the actual manuscript `coneMoment` is
controlled by the actual whole-space localized moment, with a constant
uniform for all `0 < q ≤ 9/2`. Period repetition and every Jacobian are proved. -/
theorem coneMoment_le_localized_integral (K L q : ℝ) (hK : 1 ≤ K) (hL : 0 < L)
    (hq : 0 < q) (hqu : q ≤ 9/2) (χ : SchwartzMap Space ℂ)
    (hχ : ∀ z : Space, ‖z‖ ≤ 3 → (1/2:ℝ) ≤ ‖χ z‖) (a : ℤ → ℤ → ℂ) :
    coneMoment K L q a ≤ 16 * ((K*L)^3)⁻¹ * ∫ z, ‖localized K L χ a z‖ ^ q := by
  have hKp : 0 < K := by linarith
  have hS : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKp
  have hn : 0 < (Nat.ceil K : ℝ) := by linarith [Nat.le_ceil K]
  let f : Space → ℝ := fun z => ‖localized K L χ a z‖ ^ q
  have hfi : Integrable f := localized_integrable_norm_rpow K L q hKp hL hq χ a
  have hp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm
  have hpi : Integrable (fun z : PiSpace => f (WithLp.toLp 2 z)) := hp.integrable_comp_of_integrable hfi
  have hxi : Integrable (fun x => f (WithLp.toLp 2 (physicalLinear K L x))) :=
    integrable_physical_comp K L hKp hL _ hpi
  have hxglobal : (∫ x, f (WithLp.toLp 2 (physicalLinear K L x))) =
      (1/(K*L^3*Real.sqrt K)) * ∫ z, f z := by
    rw [integral_physical_comp K L hKp hL (fun z : PiSpace => f (WithLp.toLp 2 z))]
    congr 1
    exact hp.integral_comp' f
  have hbase : IntegrableOn (fun x => ‖coneSum K L a x‖ ^ q) (enlargedBox K) := by
    apply ((Real.continuous_rpow_const hq.le).comp (ExternalInterfaces.coneSum_continuous K L a).norm).continuousOn.integrableOn_compact
    apply isCompact_univ_pi
    intro i
    fin_cases i <;> exact isCompact_Icc
  have hpoint (x : PiSpace) (hx : x ∈ enlargedBox K) :
      ‖coneSum K L a x‖ ^ q ≤ 32 * f (WithLp.toLp 2 (physicalLinear K L x)) := by
    have hcut := hχ _ (normalized_physical_norm K L hK hL x hx)
    have hnorm : ‖coneSum K L a x‖ ≤ 2 * ‖localized K L χ a (WithLp.toLp 2 (physicalLinear K L x))‖ := by
      dsimp [localized]
      rw [norm_mul, unlocalized_physical K L hKp hL]
      change _ ≤ 2 * (‖χ ((K*L)⁻¹ • WithLp.toLp 2 (physicalLinear K L x))‖ * ‖coneSum K L a x‖)
      nlinarith [norm_nonneg (coneSum K L a x)]
    calc
      _ ≤ (2 * ‖localized K L χ a (WithLp.toLp 2 (physicalLinear K L x))‖) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm hq.le
      _ = (2:ℝ)^q * f (WithLp.toLp 2 (physicalLinear K L x)) := by rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
      _ ≤ (2:ℝ)^(5:ℝ) * f (WithLp.toLp 2 (physicalLinear K L x)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
          (by dsimp [f]; positivity)
      _ = _ := by norm_num
  have hmeas : MeasurableSet (enlargedBox K) := by
    unfold enlargedBox
    apply MeasurableSet.univ_pi
    intro i
    fin_cases i <;> exact isClosed_Icc.measurableSet
  have hEn : (∫ x in enlargedBox K, ‖coneSum K L a x‖ ^ q) ≤
      32 * ((1/(K*L^3*Real.sqrt K)) * ∫ z, f z) := by
    calc
      _ ≤ ∫ x in enlargedBox K, 32 * f (WithLp.toLp 2 (physicalLinear K L x)) :=
        setIntegral_mono_on hbase (hxi.const_mul 32).integrableOn hmeas hpoint
      _ ≤ ∫ x, 32 * f (WithLp.toLp 2 (physicalLinear K L x)) :=
        setIntegral_le_integral (hxi.const_mul 32) (Filter.Eventually.of_forall (fun x => by dsimp [f]; positivity))
      _ = _ := by rw [integral_const_mul, hxglobal]
  have hIn : 0 ≤ ∫ z, f z := integral_nonneg (fun z => by dsimp [f]; positivity)
  calc
    coneMoment K L q a = (∫ x in enlargedBox K, ‖coneSum K L a x‖ ^ q) /
        (2*Real.sqrt K*(Nat.ceil K : ℝ)) := by
      rw [integral_enlargedBox K L q hq.le a]
      unfold coneMoment
      field_simp
    _ ≤ (32 * ((1/(K*L^3*Real.sqrt K)) * ∫ z, f z)) /
        (2*Real.sqrt K*(Nat.ceil K : ℝ)) := div_le_div_of_nonneg_right hEn (by positivity)
    _ = 16 * (K/(Nat.ceil K : ℝ)) * ((∫ z, f z)/(K*L)^3) := by
      field_simp
      nlinarith [Real.sq_sqrt hKp.le]
    _ ≤ 16 * 1 * ((∫ z, f z)/(K*L)^3) := by
      gcongr
      exact (div_le_one hn).mpr (Nat.le_ceil K)
    _ = _ := by dsimp [f]; ring

theorem coneFrequency_eq_frequency (K L : ℝ) (hK : 0 ≤ K) (k l : ℤ) :
    FourierLocalization.coneFrequency K L k l =
      WithLp.toLp 2 (ConeGeometry.frequency K L k l) := by
  ext i
  fin_cases i <;> simp [FourierLocalization.coneFrequency, ConeGeometry.frequency,
    Real.sqrt_div' _ hK, div_mul_eq_mul_div, div_div, mul_div_assoc, mul_comm]

end
end CircleDivisor.EnergyV3.LocalizationNormalization
