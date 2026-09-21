import CircleDivisor.EnergyV3.KernelEnvelope
import CircleDivisor.EnergyV3.AngularAtoms
import CircleDivisor.EnergyV3.AdaptedMetric

namespace CircleDivisor.EnergyV3.MetricTransport
noncomputable section
open GuthMaldague AngularAtoms
open scoped RealInnerProductSpace FourierTransform

def frameDual (R s ω : ℝ) (v : GuthMaldague.Space) : Fin 3 → ℝ :=
  ![R*s^2*⟪frameC ω, v⟫, 2*R*s*⟪frameT ω, v⟫, R*⟪frameN ω, v⟫]

theorem synthesis_adjoint_coordinates (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0)
    (v : GuthMaldague.Space) (k : Fin 3) :
    (((WeightMass.coordinateEquiv R s ω hR hs).symm :
      GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint v) k = frameDual R s ω v k := by
  have h := ContinuousLinearMap.adjoint_inner_right
    ((WeightMass.coordinateEquiv R s ω hR hs).symm :
      GuthMaldague.Space →L[ℝ] GuthMaldague.Space) (EuclideanSpace.single k 1) v
  rw [EuclideanSpace.inner_single_left] at h
  change 1 * _ = ⟪(WeightMass.coordinateEquiv R s ω hR hs).symm
    (EuclideanSpace.single k 1), v⟫ at h
  rw [WeightGeometry.coordinateEquiv_symm_apply] at h
  fin_cases k <;> simpa [frameDual, envelopeSynthesis, PiLp.single_apply, inner_add_left,
    inner_smul_left] using h

theorem frameDual_le_adjoint_norm (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0)
    (v : GuthMaldague.Space) (k : Fin 3) :
    |frameDual R s ω v k| ≤ ‖((WeightMass.coordinateEquiv R s ω hR hs).symm :
      GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint v‖ := by
  rw [← synthesis_adjoint_coordinates R s ω hR hs]
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le
    (((WeightMass.coordinateEquiv R s ω hR hs).symm :
      GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint v) k

theorem rayAngle_sin_cos (t : ℝ) (ht : 0 < t) :
    Real.cos (rayAngle t) = 2*t/(1+t^2) ∧
    Real.sin (rayAngle t) = (t^2-1)/(1+t^2) := by
  have hsq : Real.sqrt (1+((t^2-1)/(2*t))^2) = (1+t^2)/(2*t) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    field_simp
    ring
  simp only [rayAngle, Real.cos_arctan, Real.sin_arctan, hsq]
  constructor <;> field_simp <;> ring

theorem frameDual_circular (R s t : ℝ) (ht : 0 < t) (v : GuthMaldague.Space) :
    frameDual R s (rayAngle t) (LinearTransport.circularFrequency v) =
      fun k => (3/5)*AdaptedMetric.dualCoordinates R s t (fun i => v i) k := by
  obtain ⟨hc, hs⟩ := rayAngle_sin_cos t ht
  ext k
  fin_cases k <;>
    simp [frameDual, frameC, frameT, frameN, LinearTransport.circularFrequency,
      AdaptedMetric.dualCoordinates, AdaptedMetric.envelopeMatrix,
      PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hc, hs] <;>
      field_simp <;> ring

theorem frameDual_rotate (R s ω ρ : ℝ) (v : GuthMaldague.Space) :
    frameDual R s ω (rotate ρ v) = frameDual R s (ω-ρ) v := by
  ext k
  fin_cases k <;> simp [frameDual, frameC, frameT, frameN, rotate, PiLp.inner_apply,
    Fin.sum_univ_succ, Real.cos_sub, Real.sin_sub] <;> ring_nf <;> simp

theorem frame_add (ω δ : ℝ) :
    frameC (ω+δ) = ((Real.cos δ+1)/2) • frameC ω + Real.sin δ • frameT ω +
      ((Real.cos δ-1)/2) • frameN ω ∧
    frameT (ω+δ) = (-Real.sin δ/2) • frameC ω + Real.cos δ • frameT ω +
      (-Real.sin δ/2) • frameN ω ∧
    frameN (ω+δ) = ((Real.cos δ-1)/2) • frameC ω + Real.sin δ • frameT ω +
      ((Real.cos δ+1)/2) • frameN ω := by
  constructor
  · ext k; fin_cases k <;> simp [frameC, frameT, frameN, Real.cos_add, Real.sin_add] <;> ring
  constructor <;> (ext k; fin_cases k <;>
    simp [frameC, frameT, frameN, Real.cos_add, Real.sin_add] <;> ring)

theorem frameDual_shift (R s ω δ : ℝ) (hs : s ≠ 0) (v : GuthMaldague.Space) :
    frameDual R s (ω+δ) v =
      ![((Real.cos δ+1)/2) * frameDual R s ω v 0 +
          (s*Real.sin δ/2)*frameDual R s ω v 1 +
          (s^2*(Real.cos δ-1)/2)*frameDual R s ω v 2,
        (-Real.sin δ/s)*frameDual R s ω v 0 +
          Real.cos δ*frameDual R s ω v 1 + (-s*Real.sin δ)*frameDual R s ω v 2,
        ((Real.cos δ-1)/(2*s^2))*frameDual R s ω v 0 +
          (Real.sin δ/(2*s))*frameDual R s ω v 1 +
          ((Real.cos δ+1)/2)*frameDual R s ω v 2] := by
  obtain ⟨hc, ht, hn⟩ := frame_add ω δ
  ext k
  fin_cases k <;> simp [frameDual, hc, ht, hn, inner_add_left, inner_smul_left] <;>
    field_simp <;> ring

theorem cos_sub_one_bound (δ : ℝ) : |Real.cos δ-1| ≤ δ^2/2 := by
  have h := Real.sin_sq_le_sq (x := δ/2)
  have hc := Real.cos_two_mul (δ/2)
  rw [show 2*(δ/2)=δ by ring] at hc
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one δ))]
  nlinarith [Real.sin_sq_add_cos_sq (δ/2)]

theorem shift_coefficient_bounds (s δ A : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hA : 0 ≤ A) (hδ : |δ| ≤ A*s) :
    |(Real.cos δ+1)/2| ≤ (A+1)^2 ∧
    |s*Real.sin δ/2| ≤ (A+1)^2 ∧
    |s^2*(Real.cos δ-1)/2| ≤ (A+1)^2 ∧
    |-Real.sin δ/s| ≤ (A+1)^2 ∧
    |Real.cos δ| ≤ (A+1)^2 ∧
    |-s*Real.sin δ| ≤ (A+1)^2 ∧
    |(Real.cos δ-1)/(2*s^2)| ≤ (A+1)^2 ∧
    |Real.sin δ/(2*s)| ≤ (A+1)^2 := by
  have hB1 : 1 ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
  have hBA : A ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
  have hBA2 : A^2 ≤ (A+1)^2 := by nlinarith
  have hsin : |Real.sin δ| ≤ A*s := Real.abs_sin_le_abs.trans hδ
  have hss : s^2 ≤ 1 := by nlinarith
  have hcos : |Real.cos δ| ≤ 1 := Real.abs_cos_le_one δ
  have hplus : |Real.cos δ+1| ≤ 2 := (abs_add_le _ _).trans (by simpa only [abs_one] using (show |Real.cos δ|+1≤2 by linarith))
  have hminus : |Real.cos δ-1| ≤ 2 := (abs_sub _ _).trans (by simpa only [abs_one] using (show |Real.cos δ|+1≤2 by linarith))
  have hquad : |Real.cos δ-1| ≤ A^2*s^2/2 := by
    apply (cos_sub_one_bound δ).trans
    have hh : δ^2 ≤ (A*s)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg δ) (mul_nonneg hA hs.le)).mpr hδ
    nlinarith
  have hsine : |Real.sin δ|/s ≤ A := (div_le_iff₀ hs).mpr hsin
  have hsmall : s*|Real.sin δ| ≤ A := by
    calc
      _ ≤ s*(A*s) := mul_le_mul_of_nonneg_left hsin hs.le
      _ = A*s^2 := by ring
      _ ≤ A := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, hcos.trans hB1, ?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (by linarith : |Real.cos δ+1|/2 ≤ 1).trans hB1
  · rw [abs_div, abs_mul, abs_of_pos hs, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (by linarith : s*|Real.sin δ|/2 ≤ A).trans hBA
  · rw [abs_div, abs_mul, abs_pow, abs_of_pos hs, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hminus (sq_nonneg s)
    exact (by nlinarith : s^2*|Real.cos δ-1|/2 ≤ 1).trans hB1
  · simpa [abs_div, abs_neg, abs_of_pos hs] using hsine.trans hBA
  · simpa [abs_mul, abs_neg, abs_of_pos hs] using hsmall.trans hBA
  · rw [abs_div, abs_of_pos (by positivity : 0 < 2*s^2)]
    apply le_trans _ hBA2
    apply (div_le_iff₀ (by positivity : 0 < 2*s^2)).mpr
    nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg s)]
  · rw [abs_div, abs_of_pos (by positivity : 0 < 2*s)]
    apply le_trans _ hBA
    apply (div_le_iff₀ (by positivity : 0 < 2*s)).mpr
    nlinarith

theorem three_mul_bound {a b c x y z B N : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B)
    (hx : |x| ≤ N) (hy : |y| ≤ N) (hz : |z| ≤ N) :
    |a*x+b*y+c*z| ≤ 3*B*N := by
  calc
    _ ≤ (|a*x|+|b*y|)+|c*z| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (|a| * |x| + |b| * |y|) + |c| * |z| := by simp only [abs_mul]
    _ ≤ (B*N+B*N)+B*N := by gcongr
    _ = _ := by ring

theorem frameDual_nearby_bound (R s ω α A : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hA : 0 ≤ A) (hδ : |α-ω| ≤ A*s) (v : GuthMaldague.Space) (N : ℝ)
    (hN : 0 ≤ N) (hv : ∀ k, |frameDual R s ω v k| ≤ N) (k : Fin 3) :
    |frameDual R s α v k| ≤ 3*(A+1)^2*N := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := shift_coefficient_bounds s (α-ω) A hs hs1 hA hδ
  have heq : α = ω+(α-ω) := by ring
  rw [heq, frameDual_shift R s ω (α-ω) hs.ne' v]
  fin_cases k <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact three_mul_bound (sq_nonneg _) hN h0 h1 h2 (hv 0) (hv 1) (hv 2)
  · exact three_mul_bound (sq_nonneg _) hN h3 h4 h5 (hv 0) (hv 1) (hv 2)
  · exact three_mul_bound (sq_nonneg _) hN h6 h7 h0 (hv 0) (hv 1) (hv 2)

/-- The Fourier metric in the canonical circular frame controls the manuscript's
actual transpose metric centered at any ray within `A*s` of that frame. The
fixed `3/5` normalization and either grid rotation are included. -/
theorem dualCoordinates_le_rotated_adjoint (R s ω ρ t A : ℝ)
    (hR : R ≠ 0) (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (hA : 0 ≤ A)
    (hδ : |rayAngle t-(ω-ρ)| ≤ A*s) (v : GuthMaldague.Space) :
    ‖AdaptedMetric.dualCoordinates R s t (fun k => v k)‖ ≤ 5*(A+1)^2 *
      ‖((WeightMass.coordinateEquiv R s ω hR hs.ne').symm :
        GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint
          (rotate ρ (LinearTransport.circularFrequency v))‖ := by
  let N := ‖((WeightMass.coordinateEquiv R s ω hR hs.ne').symm :
        GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint
          (rotate ρ (LinearTransport.circularFrequency v))‖
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 5*(A+1)^2*N)).mpr
  intro k
  have hv (i : Fin 3) : |frameDual R s (ω-ρ) (LinearTransport.circularFrequency v) i| ≤ N := by
    rw [← frameDual_rotate R s ω ρ]
    exact frameDual_le_adjoint_norm R s ω hR hs.ne' _ i
  have hh := frameDual_nearby_bound R s (ω-ρ) (rayAngle t) A hs hs1 hA hδ
    (LinearTransport.circularFrequency v) N (norm_nonneg _) hv k
  rw [frameDual_circular R s t ht v] at hh
  simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<3/5)] at hh
  rw [Real.norm_eq_abs]
  linarith

theorem dualCoordinates_radius_mono (P R s t : ℝ) (hP : 0 ≤ P) (hR : 0 < R)
    (hPR : P ≤ R) (v : Fin 3 → ℝ) :
    ‖AdaptedMetric.dualCoordinates P s t v‖ ≤ ‖AdaptedMetric.dualCoordinates R s t v‖ := by
  have heq : AdaptedMetric.dualCoordinates P s t v =
      (P/R) • AdaptedMetric.dualCoordinates R s t v := by
    ext k
    fin_cases k <;> simp [AdaptedMetric.dualCoordinates, AdaptedMetric.envelopeMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> field_simp <;> ring
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hP hR.le)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hR).mpr hPR)

theorem canonical_metric_comparison (P A ρ t : ℝ) (n j : ℕ) (i : CapIndex j)
    (hP : 0 ≤ P) (hPR : P ≤ radius n) (ht : 0 < t) (hA : 0 ≤ A)
    (hδ : |rayAngle t-(leftEndpoint j i-ρ)| ≤ A*scale j) (v : GuthMaldague.Space) :
    ‖AdaptedMetric.dualCoordinates P (scale j) t (fun k => v k)‖ ≤ 5*(A+1)^2 *
      ‖(KernelEnvelope.synthesisEquiv n j i : GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint
        (rotate ρ (LinearTransport.circularFrequency v))‖ := by
  apply (dualCoordinates_radius_mono P (radius n) (scale j) t hP (radius_pos n) hPR _).trans
  apply dualCoordinates_le_rotated_adjoint (radius n) (scale j) (leftEndpoint j i) ρ t A
    (radius_pos n).ne' (scale_pos j) _ ht hA hδ v
  unfold scale
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

theorem circularFrequency_sub (v w : GuthMaldague.Space) :
    LinearTransport.circularFrequency (v-w) =
      LinearTransport.circularFrequency v-LinearTransport.circularFrequency w := by
  ext k
  fin_cases k <;> simp [LinearTransport.circularFrequency] <;> ring

theorem decay_comparison {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 1 ≤ C)
    (hxy : y ≤ C*x) :
    ((1+x)^8)⁻¹ ≤ C^8 * ((1+y)^8)⁻¹ := by
  have hp : (1+y)^8 ≤ C^8*(1+x)^8 := by
    calc
      _ ≤ (C*(1+x))^8 := pow_le_pow_left₀ (by positivity) (by nlinarith) 8
      _ = _ := mul_pow _ _ _
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < (1+y)^8),
    mul_comm, ← div_eq_mul_inv, div_le_iff₀ (by positivity : 0 < (1+x)^8)]
  exact hp

theorem canonical_decay_comparison (P A ρ t : ℝ) (n j : ℕ) (i : CapIndex j)
    (hP : 0 ≤ P) (hPR : P ≤ radius n) (ht : 0 < t) (hA : 0 ≤ A)
    (hδ : |rayAngle t-(leftEndpoint j i-ρ)| ≤ A*scale j) (v : GuthMaldague.Space) :
    (1 + ‖(KernelEnvelope.synthesisEquiv n j i : GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint
      (rotate ρ (LinearTransport.circularFrequency v))‖)^(-(8:ℝ)) ≤
    (5*(A+1)^2)^8 * ((1 + ‖AdaptedMetric.dualCoordinates P (scale j) t (fun k => v k)‖)^8)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
  exact decay_comparison (norm_nonneg _) (norm_nonneg _)
    (by nlinarith [sq_nonneg A])
    (canonical_metric_comparison P A ρ t n j i hP hPR ht hA hδ v)

/-- Appendix A.5 in the actual canonical envelope, with the precise arithmetic
transpose distance used by the already proved finite neighbor counts. -/
theorem transported_kernel_arithmetic_decay (χ : SchwartzMap GuthMaldague.Space ℂ)
    (C₀ A : ℝ) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) : ∃ D : ℝ, 0 < D ∧
      ∀ P : ℝ, 0 < P → ∀ E : GuthMaldague.Space →L[ℝ] GuthMaldague.Space, ‖E‖ ≤ C₀ →
      ∀ n j : ℕ, ∀ i : CapIndex j, P ≤ radius n → radius n < 4*P →
      ∀ ρ t : ℝ, 0 < t → |rayAngle t-(leftEndpoint j i-ρ)| ≤ A*scale j →
      ∀ (m : Lattice) (v : GuthMaldague.Space),
        ‖𝓕 (KernelEnvelope.transportedEnvelopeKernel χ P E n j i m)
          (rotate ρ (LinearTransport.circularFrequency v))‖ ≤
        D*envelopeVolume n j i m *
          ((1 + ‖AdaptedMetric.dualCoordinates P (scale j) t (fun k => v k)‖)^8)⁻¹ := by
  obtain ⟨D, hD, hb⟩ := KernelEnvelope.transported_envelope_kernel_decay χ C₀ 8 hC₀ (by norm_num)
  refine ⟨D*(5*(A+1)^2)^8, mul_pos hD (by positivity), ?_⟩
  intro P hP E hE n j i hPR hRP ρ t ht hδ m v
  have hh := hb P hP E hE n j i hRP m (rotate ρ (LinearTransport.circularFrequency v))
  have hd := canonical_decay_comparison P A ρ t n j i hP.le hPR ht hA hδ v
  have hV := WeightMass.envelopeVolume_pos n j i m
  calc
    _ ≤ D*envelopeVolume n j i m *
      (1 + ‖(KernelEnvelope.synthesisEquiv n j i : GuthMaldague.Space →L[ℝ] GuthMaldague.Space).adjoint
        (rotate ρ (LinearTransport.circularFrequency v))‖)^(-(8:ℝ)) := hh
    _ ≤ D*envelopeVolume n j i m * ((5*(A+1)^2)^8 *
      ((1 + ‖AdaptedMetric.dualCoordinates P (scale j) t (fun k => v k)‖)^8)⁻¹) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hD.le hV.le)
    _ = _ := by ring

end
end CircleDivisor.EnergyV3.MetricTransport
