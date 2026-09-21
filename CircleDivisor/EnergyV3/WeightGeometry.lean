import CircleDivisor.EnergyV3.WeightMass

/-! Uniform size of the actual envelope synthesis. This verifies the bounded
distortion hypothesis in the Fourier kernel estimate. -/
namespace CircleDivisor.EnergyV3.WeightGeometry
noncomputable section
open GuthMaldague
open scoped RealInnerProductSpace

theorem coordinateEquiv_symm_apply (R s ω : ℝ) (hR : R ≠ 0) (hs : s ≠ 0)
    (u : Space) :
    (WeightMass.coordinateEquiv R s ω hR hs).symm u =
      envelopeSynthesis R s ω (fun k => u k) := by
  apply (WeightMass.coordinateEquiv R s ω hR hs).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change u = WithLp.toLp 2 (envelopeCoordinates R s ω _)
  rw [envelopeCoordinates_synthesis R s ω hR hs]

theorem frame_norm_bounds (ω : ℝ) :
    ‖frameC ω‖ ≤ 2 ∧ ‖frameT ω‖ ≤ 1 ∧ ‖frameN ω‖ ≤ 2 := by
  obtain ⟨hc, ht, hn, _⟩ := frame_inner_values ω
  rw [real_inner_self_eq_norm_sq] at hc ht hn
  exact ⟨by nlinarith [norm_nonneg (frameC ω)],
    by nlinarith [norm_nonneg (frameT ω)], by nlinarith [norm_nonneg (frameN ω)]⟩

theorem envelopeSynthesis_norm_le (R s ω : ℝ) (hR : 0 ≤ R) (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (u : Space) :
    ‖envelopeSynthesis R s ω (fun k => u k)‖ ≤ 6*R*‖u‖ := by
  have hu (k : Fin 3) : |u k| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u k
  obtain ⟨hc, ht, hn⟩ := frame_norm_bounds ω
  have hs2 : s^2 ≤ 1 := by nlinarith
  calc
    _ ≤ ‖(R*s^2*u 0) • frameC ω‖ + ‖(2*R*s*u 1) • frameT ω‖ +
        ‖(R*u 2) • frameN ω‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = R*s^2*|u 0| * ‖frameC ω‖ + 2*R*s*|u 1| * ‖frameT ω‖ +
        R*|u 2| * ‖frameN ω‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hR,
        abs_of_nonneg hs, abs_of_nonneg (sq_nonneg s), abs_of_nonneg (show (0:ℝ)≤2 by norm_num)]
    _ ≤ R*1*‖u‖*2 + 2*R*1*‖u‖*1 + R*‖u‖*2 := by gcongr <;> exact hu _
    _ = _ := by ring

theorem coordinateEquiv_symm_norm_le (R s ω : ℝ) (hR : 0 < R) (hs : 0 < s)
    (hs1 : s ≤ 1) :
    ‖((WeightMass.coordinateEquiv R s ω hR.ne' hs.ne').symm : Space →L[ℝ] Space)‖ ≤ 6*R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖(WeightMass.coordinateEquiv R s ω hR.ne' hs.ne').symm u‖ ≤ _
  rw [coordinateEquiv_symm_apply]
  exact envelopeSynthesis_norm_le R s ω hR.le hs.le hs1 u

theorem canonical_synthesis_norm_le (P : ℝ) (n j : ℕ) (i : CapIndex j)
    (hR : radius n < 4*P) :
    ‖((WeightMass.coordinateEquiv (radius n) (scale j) (leftEndpoint j i)
      (radius_pos n).ne' (scale_pos j).ne').symm : Space →L[ℝ] Space)‖ ≤ 24*P := by
  have hs : scale j ≤ 1 := by
    unfold scale
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  exact (coordinateEquiv_symm_norm_le _ _ _ (radius_pos n) (scale_pos j) hs).trans (by linarith)

end
end CircleDivisor.EnergyV3.WeightGeometry
