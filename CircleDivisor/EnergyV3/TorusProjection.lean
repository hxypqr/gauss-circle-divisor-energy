import Mathlib

/-! The actual probability Haar integrals in the weighted projection principle.
No orthogonality or finite-window estimate is an assumed interface. -/
namespace CircleDivisor.EnergyV3.TorusProjection
open MeasureTheory Finset
open scoped ComplexConjugate
noncomputable section

abbrev Torus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)
abbrev Frequency := ℤ × ℤ
def haar : Measure Torus := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle
instance : IsProbabilityMeasure haar := by unfold haar; infer_instance

def character (d : Frequency) (u : Torus) : ℂ :=
  fourier d.1 u.1 * fourier d.2 u.2

theorem continuous_character (d : Frequency) : Continuous (character d) :=
  ((fourier d.1).continuous.comp continuous_fst).mul
    ((fourier d.2).continuous.comp continuous_snd)

theorem integrable_continuous {f : Torus → ℂ} (hf : Continuous f) : Integrable f haar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem circle_orthogonality (m n : ℤ) :
    (∫ u : AddCircle (1 : ℝ), fourier m u * conj (fourier n u)
      ∂AddCircle.haarAddCircle) = if m = n then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) m) n
  simpa [fourierCoeff, fourier_neg, smul_eq_mul, mul_comm,
    Pi.single_apply, eq_comm] using h

theorem character_orthogonality (d e : Frequency) :
    (∫ u, character d u * conj (character e u) ∂haar) = if d = e then 1 else 0 := by
  have hfun : (fun u => character d u * conj (character e u)) =
      (fun u : Torus =>
        (fourier d.1 u.1 * conj (fourier e.1 u.1)) *
        (fourier d.2 u.2 * conj (fourier e.2 u.2))) := by
    funext u
    simp only [character, map_mul]
    ring
  rw [hfun]
  have hp := integral_prod_mul (μ := AddCircle.haarAddCircle) (ν := AddCircle.haarAddCircle)
    (fun u : AddCircle (1 : ℝ) => fourier d.1 u * conj (fourier e.1 u))
    (fun u : AddCircle (1 : ℝ) => fourier d.2 u * conj (fourier e.2 u))
  change (∫ u, _ ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) = _
  rw [hp, circle_orthogonality, circle_orthogonality]
  by_cases h1 : d.1 = e.1 <;> by_cases h2 : d.2 = e.2 <;>
    simp [h1, h2, Prod.ext_iff]

theorem character_norm (d : Frequency) (u : Torus) : ‖character d u‖ = 1 := by
  simp [character, norm_mul, fourier_norm]

def polynomial {ι : Type*} (S : Finset ι) (freq : ι → Frequency) (b : ι → ℂ) (u : Torus) : ℂ :=
  ∑ i ∈ S, b i * character (freq i) u

theorem continuous_polynomial {ι : Type*} (S : Finset ι) (freq : ι → Frequency) (b : ι → ℂ) :
    Continuous (polynomial S freq b) := by
  apply continuous_finset_sum
  intro i hi
  exact continuous_const.mul (continuous_character (freq i))

theorem integral_norm_sq_expansion {ι : Type*} (S : Finset ι)
    (freq : ι → Frequency) (b : ι → ℂ) :
    (∫ u, ‖polynomial S freq b u‖ ^ 2 ∂haar) =
      ∑ i ∈ S, ∑ j ∈ S, if freq i = freq j then (b i * conj (b j)).re else 0 := by
  have hpoint u : ‖polynomial S freq b u‖ ^ 2 =
      (polynomial S freq b u * conj (polynomial S freq b u)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hc (i j : ι) : Integrable (fun u =>
      (b i * character (freq i) u) * conj (b j * character (freq j) u)) haar := by
    apply integrable_continuous
    exact (continuous_const.mul (continuous_character _)).mul
      (Complex.continuous_conj.comp (continuous_const.mul (continuous_character _)))
  simp_rw [hpoint, polynomial, map_sum, Finset.sum_mul, Finset.mul_sum,
    Complex.re_sum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j hj
      calc
        _ = (∫ u, (b i * character (freq i) u) * conj (b j * character (freq j) u) ∂haar).re :=
          integral_re (hc i j)
        _ = _ := ?_
      have hh : (fun u => (b i * character (freq i) u) * conj (b j * character (freq j) u)) =
          (fun u => (b i * conj (b j)) * (character (freq i) u * conj (character (freq j) u))) := by
        funext u
        simp only [map_mul]
        ring
      rw [hh, integral_const_mul, character_orthogonality]
      split_ifs <;> simp
    · exact fun j hj => (hc i j).re
  · exact fun i hi => integrable_finsetSum S (fun j hj => (hc i j).re)

def matchingPairs {ι : Type*} (S : Finset ι) (freq : ι → Frequency) : Finset (ι × ι) :=
  (S ×ˢ S).filter (fun ij => freq ij.1 = freq ij.2)

theorem weighted_projection_bound {ι : Type*} (S : Finset ι) (freq : ι → Frequency)
    (b : ι → ℂ) (hb : ∀ i ∈ S, ‖b i‖ ≤ 1) :
    (∫ u, ‖polynomial S freq b u‖ ^ 2 ∂haar) ≤ (matchingPairs S freq).card := by
  rw [integral_norm_sq_expansion]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, if freq i = freq j then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      split_ifs
      · calc
          _ ≤ ‖b i * conj (b j)‖ := Complex.re_le_norm _
          _ = ‖b i‖ * ‖b j‖ := by rw [norm_mul, Complex.norm_conj]
          _ ≤ 1 := by nlinarith [norm_nonneg (b i), norm_nonneg (b j), hb i hi, hb j hj]
      · rfl
    _ = ∑ p ∈ S ×ˢ S, if freq p.1 = freq p.2 then (1 : ℝ) else 0 :=
      (sum_product S S (fun p => if freq p.1 = freq p.2 then (1 : ℝ) else 0)).symm
    _ = _ := by rw [← sum_filter]; simp [matchingPairs]

theorem parseval_injective {ι : Type*} (S : Finset ι) (freq : ι → Frequency)
    (b : ι → ℂ) (hi : Set.InjOn freq (S : Set ι)) :
    (∫ u, ‖polynomial S freq b u‖ ^ 2 ∂haar) = ∑ i ∈ S, ‖b i‖ ^ 2 := by
  classical
  rw [integral_norm_sq_expansion]
  apply sum_congr rfl
  intro i hiS
  rw [sum_eq_single i]
  · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
  · intro j hj hji
    have hf : freq i ≠ freq j := fun h => hji (hi hiS hj h).symm
    simp [hf]
  · simp [hiS]

def fiberCoefficient {ι : Type*} (S : Finset ι) (freq : ι → Frequency) (b : ι → ℂ)
    (d : Frequency) : ℂ := ∑ i ∈ S with freq i = d, b i

theorem polynomial_group_by_frequency {ι : Type*} (S : Finset ι)
    (freq : ι → Frequency) (b : ι → ℂ) :
    polynomial S freq b = polynomial (S.image freq) id (fiberCoefficient S freq b) := by
  classical
  funext u
  unfold polynomial fiberCoefficient
  have hh := sum_fiberwise_of_maps_to (s := S) (t := S.image freq) (fun i hi => mem_image_of_mem freq hi)
    (fun i => b i * character (freq i) u)
  rw [← hh]
  apply sum_congr rfl
  intro d hd
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]
  rfl

/-- Parseval with the exact finite frequency fibers; frequencies outside this
image have zero multiplicity and zero coefficient. -/
theorem weighted_projection_identity {ι : Type*} (S : Finset ι)
    (freq : ι → Frequency) (b : ι → ℂ) :
    (∫ u, ‖polynomial S freq b u‖ ^ 2 ∂haar) =
      ∑ d ∈ S.image freq, ‖fiberCoefficient S freq b d‖ ^ 2 := by
  rw [polynomial_group_by_frequency]
  exact parseval_injective _ id _ (Function.injective_id.injOn)

theorem fiberCoefficient_norm_le_card {ι : Type*} (S : Finset ι)
    (freq : ι → Frequency) (b : ι → ℂ) (hb : ∀ i ∈ S, ‖b i‖ ≤ 1) (d : Frequency) :
    ‖fiberCoefficient S freq b d‖ ≤ (S.filter (fun i => freq i = d)).card := by
  calc
    _ ≤ ∑ i ∈ S.filter (fun i => freq i = d), ‖b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S.filter (fun i => freq i = d), (1 : ℝ) :=
      sum_le_sum (fun i hi => hb i (mem_filter.mp hi).1)
    _ = _ := by simp

theorem weighted_projection_le_fiber_energy {ι : Type*} (S : Finset ι)
    (freq : ι → Frequency) (b : ι → ℂ) (hb : ∀ i ∈ S, ‖b i‖ ≤ 1) :
    (∫ u, ‖polynomial S freq b u‖ ^ 2 ∂haar) ≤
      ∑ d ∈ S.image freq, ((S.filter (fun i => freq i = d)).card : ℝ) ^ 2 := by
  rw [weighted_projection_identity]
  apply sum_le_sum
  intro d hd
  exact pow_le_pow_left₀ (norm_nonneg _) (fiberCoefficient_norm_le_card S freq b hb d) 2

end
end CircleDivisor.EnergyV3.TorusProjection
