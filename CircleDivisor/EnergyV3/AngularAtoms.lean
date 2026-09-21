import CircleDivisor.AngularGrid
import CircleDivisor.GuthMaldagueInput
import CircleDivisor.EnergyV3.LocalizationNormalization
import CircleDivisor.EnergyV3.NeighborCount

namespace CircleDivisor.EnergyV3.AngularAtoms
open MeasureTheory
open scoped RealInnerProductSpace
noncomputable section
abbrev Space := FourierLocalization.Space

theorem arctan_lipschitz : LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
  intro x
  change ‖deriv Real.arctan x‖ ≤ (1 : ℝ)
  rw [Real.deriv_arctan, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg x])

theorem arctan_sub_le (x y : ℝ) : |Real.arctan x - Real.arctan y| ≤ |x-y| := by
  simpa [Real.dist_eq] using arctan_lipschitz.dist_le_mul x y

theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) : z.arg = Real.arctan (z.im/z.re) := by
  rw [← Complex.tan_arg]
  exact (Real.arctan_tan (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))).symm

/-- An explicit angular perturbation bound on the fixed right-half-plane arc.
Both points here are actual complex coordinates, with no angular regularity input. -/
theorem arg_perturb (z c : ℂ) (e : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/4)
    (hc : 1/2 ≤ c.re) (hci : |c.im| ≤ 1)
    (hre : |z.re-c.re| ≤ e) (him : |z.im-c.im| ≤ e) :
    |z.arg-c.arg| ≤ 12*e := by
  have hcpos : 0 < c.re := by linarith
  have hz : 1/4 ≤ z.re := by linarith [(abs_le.mp hre).1]
  have hzpos : 0 < z.re := by linarith
  rw [arg_eq_arctan hzpos, arg_eq_arctan hcpos]
  apply (arctan_sub_le _ _).trans
  have hid : z.im/z.re-c.im/c.re =
      (z.im-c.im)/z.re + c.im*(c.re-z.re)/(z.re*c.re) := by field_simp; ring
  rw [hid]
  calc
    _ ≤ |(z.im-c.im)/z.re| + |c.im*(c.re-z.re)/(z.re*c.re)| := abs_add_le _ _
    _ ≤ 4*e + 8*e := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hzpos]
        apply (div_le_iff₀ hzpos).mpr
        nlinarith
      · rw [abs_div, abs_mul, abs_sub_comm, abs_of_pos (mul_pos hzpos hcpos)]
        apply (div_le_iff₀ (mul_pos hzpos hcpos)).mpr
        have hn : |c.im| * |z.re-c.re| ≤ e := by nlinarith [abs_nonneg c.im, abs_nonneg (z.re-c.re)]
        have hd : 1/8 ≤ z.re*c.re := by nlinarith
        nlinarith
    _ = _ := by ring

def complexXY (v : Space) : ℂ := (v 0 : ℂ)+(v 1 : ℂ)*Complex.I

@[simp] theorem complexXY_re (v : Space) : (complexXY v).re = v 0 := by simp [complexXY]
@[simp] theorem complexXY_im (v : Space) : (complexXY v).im = v 1 := by simp [complexXY]

theorem coordinate_perturb (v w : Space) (i : Fin 3) : |v i-w i| ≤ ‖v-w‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (v-w) i

def generator (r t : ℝ) : Space :=
  WithLp.toLp 2 ![(3/5)*r*t, (3/5)*r*((t^2-1)/2), (3/5)*r*((t^2+1)/2)]

def rayAngle (t : ℝ) : ℝ := Real.arctan ((t^2-1)/(2*t))

theorem generator_angle (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    (complexXY (generator r t)).arg = rayAngle t := by
  rw [arg_eq_arctan (by rw [complexXY_re]; change 0 < (3/5)*r*t; positivity)]
  congr 1
  rw [complexXY_im, complexXY_re]
  change ((3/5)*r*((t^2-1)/2))/((3/5)*r*t) = (t^2-1)/(2*t)
  field_simp

theorem rayAngle_bounds (t : ℝ) (ht : 1 ≤ t) (htu : t^2 ≤ 2) :
    0 ≤ rayAngle t ∧ rayAngle t ≤ 1/2 := by
  have htp : 0 < t := by linarith
  have hn : 0 ≤ (t^2-1)/(2*t) := div_nonneg (by nlinarith) (by positivity)
  have hu : (t^2-1)/(2*t) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have ha : 0 ≤ rayAngle t := Real.arctan_nonneg.mpr hn
  refine ⟨ha, ?_⟩
  have hb := arctan_sub_le ((t^2-1)/(2*t)) 0
  change 0 ≤ Real.arctan ((t^2-1)/(2*t)) at ha
  change Real.arctan ((t^2-1)/(2*t)) ≤ 1/2
  rw [Real.arctan_zero, sub_zero, sub_zero, abs_of_nonneg hn, abs_of_nonneg ha] at hb
  exact hb.trans hu

theorem generator_mem_cone (r t : ℝ) (hr : 1 ≤ r) (hru : r < 2)
    (ht : 1 ≤ t) (htu : t^2 < 2) : generator r t ∈ GuthMaldague.cone := by
  change ((3/5)*r*t)^2+((3/5)*r*((t^2-1)/2))^2 = ((3/5)*r*((t^2+1)/2))^2 ∧
    (1/2:ℝ) ≤ (3/5)*r*((t^2+1)/2) ∧ (3/5)*r*((t^2+1)/2) ≤ 2
  constructor
  · ring
  constructor <;> nlinarith [sq_nonneg t, mul_nonneg (by linarith : 0 ≤ r-1) (by nlinarith : 0 ≤ t^2-1)]

theorem generator_arg_perturb (r t e : ℝ) (hr : 1 ≤ r) (hru : r < 2)
    (ht : 1 ≤ t) (htu : t^2 < 2) (he : 0 ≤ e) (heu : e ≤ 1/4)
    (v : Space) (hv : ‖v-generator r t‖ ≤ e) :
    |(complexXY v).arg-rayAngle t| ≤ 12*e := by
  rw [← generator_angle r t (by linarith) (by linarith)]
  apply arg_perturb _ _ e he heu
  · rw [complexXY_re]
    change 1/2 ≤ (3/5)*r*t
    nlinarith
  · rw [complexXY_im]
    change |(3/5)*r*((t^2-1)/2)| ≤ 1
    have htn : 0 ≤ t^2-1 := by nlinarith
    rw [abs_of_nonneg (by positivity)]
    have hmul : r*(t^2-1) < 2 := by nlinarith
    nlinarith
  · simpa only [complexXY_re] using (coordinate_perturb v (generator r t) 0).trans hv
  · simpa only [complexXY_im] using (coordinate_perturb v (generator r t) 1).trans hv

def rotate (ρ : ℝ) (v : Space) : Space := WithLp.toLp 2
  ![Real.cos ρ*v 0-Real.sin ρ*v 1, Real.sin ρ*v 0+Real.cos ρ*v 1, v 2]

theorem rotate_complexXY (ρ : ℝ) (v : Space) :
    complexXY (rotate ρ v) = ((Real.cos ρ : ℂ)+(Real.sin ρ : ℂ)*Complex.I)*complexXY v := by
  apply Complex.ext <;> simp [complexXY, rotate] <;> ring

theorem rotate_norm (ρ : ℝ) (v : Space) : ‖rotate ρ v‖ = ‖v‖ := by
  have ha := EuclideanSpace.real_norm_sq_eq (rotate ρ v)
  have hb := EuclideanSpace.real_norm_sq_eq v
  simp [rotate, Fin.sum_univ_succ] at ha hb
  change ‖rotate ρ v‖^2 = (Real.cos ρ*v 0-Real.sin ρ*v 1)^2+
    ((Real.sin ρ*v 0+Real.cos ρ*v 1)^2+v 2^2) at ha
  have hid : (Real.cos ρ*v 0-Real.sin ρ*v 1)^2+
      ((Real.sin ρ*v 0+Real.cos ρ*v 1)^2+v 2^2) =
      (Real.sin ρ^2+Real.cos ρ^2)*(v 0^2+v 1^2)+v 2^2 := by ring
  rw [hid, Real.sin_sq_add_cos_sq, one_mul] at ha
  nlinarith [norm_nonneg v, norm_nonneg (rotate ρ v)]

theorem rotate_sub (ρ : ℝ) (v w : Space) : rotate ρ (v-w) = rotate ρ v-rotate ρ w := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

theorem rotate_mem_cone (ρ : ℝ) {v : Space} (hv : v ∈ GuthMaldague.cone) :
    rotate ρ v ∈ GuthMaldague.cone := by
  rcases hv with ⟨hquad,hlo,hhi⟩
  refine ⟨?_,hlo,hhi⟩
  change (Real.cos ρ*v 0-Real.sin ρ*v 1)^2+(Real.sin ρ*v 0+Real.cos ρ*v 1)^2 = v 2^2
  have hid : (Real.cos ρ*v 0-Real.sin ρ*v 1)^2+(Real.sin ρ*v 0+Real.cos ρ*v 1)^2 =
      (Real.sin ρ^2+Real.cos ρ^2)*(v 0^2+v 1^2) := by ring
  rw [hid, Real.sin_sq_add_cos_sq, one_mul]
  exact hquad

theorem rotated_angle (ρ : ℝ) (v : Space) (hv : complexXY v ≠ 0)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1) (ha : 0 ≤ (complexXY v).arg+ρ)
    (hau : (complexXY v).arg+ρ ≤ 2) :
    GuthMaldague.cylindricalAngle (rotate ρ v) = (complexXY v).arg+ρ := by
  have hunit : ((Real.cos ρ : ℂ)+(Real.sin ρ : ℂ)*Complex.I) ≠ 0 := by
    intro heq
    have hh := Complex.norm_cos_add_sin_mul_I ρ
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hh
    rw [heq, norm_zero] at hh
    norm_num at hh
  have harg : (((Real.cos ρ : ℂ)+(Real.sin ρ : ℂ)*Complex.I)).arg = ρ :=
    by simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      (Complex.arg_cos_add_sin_mul_I (θ := ρ) ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩)
  have heq : (complexXY (rotate ρ v)).arg = (complexXY v).arg+ρ := by
    rw [rotate_complexXY, Complex.arg_mul hunit hv]
    · rw [harg]; ring
    · rw [harg]
      constructor <;> linarith [Real.pi_gt_three]
  change (if (complexXY (rotate ρ v)).arg < 0 then
    (complexXY (rotate ρ v)).arg+2*Real.pi else (complexXY (rotate ρ v)).arg) = _
  rw [heq, if_neg (not_lt.mpr ha)]

def gridRotation (δ : ℝ) (b : Bool) : ℝ := δ*(1-AngularGrid.offset b)

theorem gridRotation_bounds (δ : ℝ) (hδ : 0 ≤ δ) (b : Bool) :
    δ/2 ≤ gridRotation δ b ∧ gridRotation δ b ≤ δ := by
  cases b <;> simp only [gridRotation, AngularGrid.offset, Bool.false_eq_true, if_false, if_true]
  all_goals constructor <;> linarith

theorem rotated_floor_same (δ x y : ℝ) (hδ : 0 < δ) (b : Bool)
    (hsafe : ∀ m : ℤ, δ/4 ≤ |x-δ*((m:ℝ)+AngularGrid.offset b)|)
    (hnear : |y-x| < δ/8) :
    ⌊(y+gridRotation δ b)/δ⌋ = ⌊(x+gridRotation δ b)/δ⌋ := by
  have hh := AngularGrid.same_cell_of_safe_grid δ x y hδ b hsafe hnear
  have hrot (u : ℝ) : (u+gridRotation δ b)/δ = (u/δ-AngularGrid.offset b)+1 := by
    unfold gridRotation
    field_simp
    ring
  rw [hrot, hrot, Int.floor_add_one, Int.floor_add_one, hh]

def angularWidth (n : ℕ) : ℝ := 2*Real.pi*GuthMaldague.scale n

theorem angularWidth_pos (n : ℕ) : 0 < angularWidth n := by
  unfold angularWidth
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (GuthMaldague.scale_pos n)

theorem angularInterval_iff_floor (n : ℕ) (i : GuthMaldague.CapIndex n) (x : ℝ) :
    x ∈ GuthMaldague.angularInterval n i ↔ ⌊x/angularWidth n⌋ = (i.val : ℤ) := by
  rw [Int.floor_eq_iff]
  have hd := angularWidth_pos n
  change (2*Real.pi*(i.val:ℝ)*GuthMaldague.scale n ≤ x ∧
      x < 2*Real.pi*(i.val:ℝ)*GuthMaldague.scale n+2*Real.pi*GuthMaldague.scale n) ↔ _
  have he : 2*Real.pi*(i.val:ℝ)*GuthMaldague.scale n = angularWidth n*(i.val:ℝ) := by unfold angularWidth; ring
  rw [he]
  simp only [Int.cast_natCast]
  constructor
  · intro hx
    constructor
    · exact (le_div_iff₀ hd).mpr (by nlinarith [hx.1])
    · exact (div_lt_iff₀ hd).mpr (by dsimp [angularWidth] at *; nlinarith [hx.2])
  · intro hx
    constructor
    · have hh := (le_div_iff₀ hd).mp hx.1; nlinarith
    · have hh := (div_lt_iff₀ hd).mp hx.2; dsimp [angularWidth] at *; nlinarith

theorem exists_angular_cap (n : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxu : x < 2*Real.pi) :
    ∃ i : GuthMaldague.CapIndex n, x ∈ GuthMaldague.angularInterval n i := by
  have hd := angularWidth_pos n
  have hfloor : 0 ≤ ⌊x/angularWidth n⌋ := Int.floor_nonneg.mpr (div_nonneg hx hd.le)
  have hlt : ⌊x/angularWidth n⌋ < (2^n : ℕ) := by
    apply Int.floor_lt.mpr
    rw [div_lt_iff₀ hd]
    simp only [angularWidth, GuthMaldague.scale, Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat]
    have heq : (2:ℝ)^n*(2*Real.pi*((2:ℝ)^n)⁻¹) = 2*Real.pi := by field_simp
    rw [heq]
    exact hxu
  let i : GuthMaldague.CapIndex n := ⟨⌊x/angularWidth n⌋.toNat, by omega⟩
  refine ⟨i, (angularInterval_iff_floor n i x).mpr ?_⟩
  exact (Int.toNat_of_nonneg hfloor).symm

/-- Two actual rotations put every point of the entire Fourier atom in one
canonical GM cap. The choice of rotation and cap depends only on the ray `t`,
and holds simultaneously for every radial parameter `1 ≤ r < 2`. -/
theorem whole_ray_atoms_one_cap (n : ℕ) (t e : ℝ)
    (ht : 1 ≤ t) (htu : t^2 < 2) (he : 0 ≤ e) (heu : e ≤ 1/4)
    (hδ : angularWidth n ≤ 1/4) (hsmall : 12*e < angularWidth n/8)
    (hcone : e < GuthMaldague.scale n^2) :
    ∃ b : Bool, ∃ i : GuthMaldague.CapIndex n,
      ∀ r : ℝ, 1 ≤ r → r < 2 → ∀ v : Space, ‖v-generator r t‖ ≤ e →
        rotate (gridRotation (angularWidth n) b) v ∈ GuthMaldague.cap n i := by
  have hd := angularWidth_pos n
  obtain ⟨b,hb⟩ := AngularGrid.safe_grid (angularWidth n) (rayAngle t) hd
  let ρ := gridRotation (angularWidth n) b
  have hρ := gridRotation_bounds (angularWidth n) hd.le b
  have htangle := rayAngle_bounds t ht htu.le
  have hx : 0 ≤ rayAngle t+ρ := by dsimp [ρ]; linarith
  have hxu : rayAngle t+ρ < 2*Real.pi := by dsimp [ρ]; linarith [Real.pi_gt_three]
  obtain ⟨i,hi⟩ := exists_angular_cap n (rayAngle t+ρ) hx hxu
  refine ⟨b,i,fun r hr hru v hv => ?_⟩
  have hnear := generator_arg_perturb r t e hr hru ht htu he heu v hv
  have hnear' : |(complexXY v).arg-rayAngle t| < angularWidth n/8 := hnear.trans_lt hsmall
  have hnz : complexXY v ≠ 0 := by
    intro hz
    have hh := (coordinate_perturb v (generator r t) 0).trans hv
    have hzero : v 0 = 0 := by simpa only [complexXY_re, Complex.zero_re] using congrArg Complex.re hz
    change |v 0-(3/5)*r*t| ≤ e at hh
    rw [hzero] at hh
    nlinarith [(abs_le.mp hh).1]
  have ha : GuthMaldague.cylindricalAngle (rotate ρ v) = (complexXY v).arg+ρ := by
    apply rotated_angle ρ v hnz <;> dsimp [ρ] at * <;>
      linarith [(abs_le.mp hnear).1, (abs_le.mp hnear).2]
  refine ⟨?_, ?_⟩
  · refine ⟨rotate ρ (generator r t), rotate_mem_cone ρ (generator_mem_cone r t hr hru ht htu), ?_⟩
    rw [dist_eq_norm, ← rotate_sub, rotate_norm]
    exact hv.trans_lt hcone
  · change GuthMaldague.cylindricalAngle (rotate ρ v) ∈ GuthMaldague.angularInterval n i
    rw [ha, angularInterval_iff_floor, rotated_floor_same (angularWidth n) (rayAngle t) _ hd b hb hnear']
    exact (angularInterval_iff_floor n i (rayAngle t+ρ)).mp hi

theorem arctan_inverse_bound (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2))
    (hy : y ∈ Set.Icc (0:ℝ) (1/2)) : |x-y| ≤ 2*|Real.arctan x-Real.arctan y| := by
  have hder (z : ℝ) (hz : z ∈ interior (Set.Icc (0:ℝ) (1/2))) :
      (1/2:ℝ) ≤ deriv Real.arctan z := by
    have hz' := interior_subset hz
    rw [Real.deriv_arctan]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [hz'.1,hz'.2]
  have hh := (convex_Icc (0:ℝ) (1/2)).mul_sub_le_image_sub_of_le_deriv
    Real.continuous_arctan.continuousOn Real.differentiable_arctan.differentiableOn hder
  rcases le_total x y with hxy|hyx
  · have hb := hh x hx y hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (Real.arctan_strictMono.monotone hxy))]
    linarith
  · have hb := hh y hy x hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (Real.arctan_strictMono.monotone hyx))]
    linarith

/-- The actual angular coordinate has a uniformly Lipschitz inverse on the
whole arithmetic arc. This supplies the fine and coarse `k`-diameter bounds. -/
theorem parameter_angle_separation (t u : ℝ) (ht : 1 ≤ t) (htu : t^2 ≤ 2)
    (hu : 1 ≤ u) (huu : u^2 ≤ 2) : |t-u| ≤ 4*|rayAngle t-rayAngle u| := by
  have htp : 0 < t := by linarith
  have hup : 0 < u := by linarith
  have hm : 0 < t*u := mul_pos htp hup
  have hbounds (v : ℝ) (hv : 1 ≤ v) (hvu : v^2 ≤ 2) :
      (v^2-1)/(2*v) ∈ Set.Icc (0:ℝ) (1/2) := by
    constructor
    · exact div_nonneg (by nlinarith) (by linarith)
    · exact (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have ha := arctan_inverse_bound _ _ (hbounds t ht htu) (hbounds u hu huu)
  change |(t^2-1)/(2*t)-(u^2-1)/(2*u)| ≤ 2*|rayAngle t-rayAngle u| at ha
  have he : (t^2-1)/(2*t)-(u^2-1)/(2*u) = (t-u)*(1+1/(t*u))/2 := by field_simp; ring
  rw [he, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 1+1/(t*u))] at ha
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)] at ha
  have hi : 0 ≤ 1/(t*u) := by positivity
  nlinarith [abs_nonneg (t-u), mul_nonneg (abs_nonneg (t-u)) hi]

theorem index_angle_separation (K k j : ℝ) (hK : 0 < K)
    (hk : K ≤ k) (hku : k < 2*K) (hj : K ≤ j) (hju : j < 2*K) :
    |k-j| ≤ 16*K*|rayAngle (Real.sqrt (k/K))-rayAngle (Real.sqrt (j/K))| := by
  have hkp := NeighborCount.sqrt_parameter_bounds hK hk hku
  have hjp := NeighborCount.sqrt_parameter_bounds hK hj hju
  have ht := parameter_angle_separation _ _ hkp.1 (by nlinarith [hkp.2.2])
    hjp.1 (by nlinarith [hjp.2.2])
  have hh := NeighborCount.index_distance_of_parameter_distance hK hk hku hj hju ht
  nlinarith

theorem circularFrequency_generator (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (k l : ℤ) (hk : K ≤ k) :
    LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L k l) =
      generator ((l:ℝ)/L) (Real.sqrt ((k:ℝ)/K)) := by
  rw [LocalizationNormalization.coneFrequency_eq_frequency K L hK.le]
  have hsq : (Real.sqrt ((k:ℝ)/K))^2 = (k:ℝ)/K := Real.sq_sqrt (div_nonneg (by linarith) hK.le)
  ext i
  fin_cases i <;> simp [LinearTransport.circularFrequency, ConeGeometry.frequency, generator, hsq] <;> ring

theorem rotate_neg_rotate (ρ : ℝ) (v : Space) : rotate (-ρ) (rotate ρ v) = v := by
  ext i
  fin_cases i <;> simp [rotate, Real.cos_neg, Real.sin_neg]
  · nlinarith [congrArg (fun a : ℝ => a*v 0) (Real.sin_sq_add_cos_sq ρ)]
  · nlinarith [congrArg (fun a : ℝ => a*v 1) (Real.sin_sq_add_cos_sq ρ)]

theorem cap_disjoint (n : ℕ) {i j : GuthMaldague.CapIndex n} (hij : i ≠ j) :
    Disjoint (GuthMaldague.cap n i) (GuthMaldague.cap n j) := by
  apply Set.disjoint_left.mpr
  intro v hv hi
  have h1 := (angularInterval_iff_floor n i _).mp hv.2
  have h2 := (angularInterval_iff_floor n j _).mp hi.2
  apply hij
  apply Fin.ext
  exact_mod_cast h1.symm.trans h2

theorem rotated_ball_subset_cap (n : ℕ) (t e : ℝ)
    (ht : 1 ≤ t) (htu : t^2 < 2) (he : 0 ≤ e) (heu : e ≤ 1/4)
    (hδ : angularWidth n ≤ 1/4) (hsmall : 12*e < angularWidth n/8)
    (hcone : e < GuthMaldague.scale n^2) :
    ∃ b : Bool, ∃ i : GuthMaldague.CapIndex n,
      ∀ r : ℝ, 1 ≤ r → r < 2 →
        Metric.ball (rotate (gridRotation (angularWidth n) b) (generator r t)) e ⊆
          GuthMaldague.cap n i := by
  obtain ⟨b,i,hi⟩ := whole_ray_atoms_one_cap n t e ht htu he heu hδ hsmall hcone
  refine ⟨b,i,fun r hr hru v hv => ?_⟩
  let ρ := gridRotation (angularWidth n) b
  have hdist : ‖rotate (-ρ) v-generator r t‖ ≤ e := by
    rw [← rotate_neg_rotate ρ (generator r t), ← rotate_sub, rotate_norm]
    exact (Metric.mem_ball.mp hv).le
  have hh := hi r hr hru (rotate (-ρ) v) hdist
  have heq : rotate ρ (rotate (-ρ) v) = v := by
    simpa using rotate_neg_rotate (-ρ) v
  rwa [heq] at hh

theorem dyadic_bounds (K : ℝ) (k : ℤ) (hk : k ∈ dyadicIntegers K) :
    K ≤ (k:ℝ) ∧ (k:ℝ) < 2*K := by
  rcases Finset.mem_Ico.mp hk with ⟨hlo,hhi⟩
  exact ⟨Int.ceil_le.mp hlo, Int.lt_ceil.mp hhi⟩

theorem exists_ray_assignment (K L : ℝ) (hK : 0 < K) (hL : 0 < L) (n : ℕ) (e : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/4) (hδ : angularWidth n ≤ 1/4)
    (hsmall : 12*e < angularWidth n/8) (hcone : e < GuthMaldague.scale n^2) :
    ∃ b : ℤ → Bool, ∃ θ : ℤ → GuthMaldague.CapIndex n,
      ∀ k ∈ dyadicIntegers K, ∀ l ∈ dyadicIntegers L,
        Metric.ball (rotate (gridRotation (angularWidth n) (b k))
          (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L k l))) e ⊆
            GuthMaldague.cap n (θ k) := by
  classical
  have hall (k : ℤ) : ∃ b : Bool, ∃ θ : GuthMaldague.CapIndex n,
      k ∈ dyadicIntegers K → ∀ l ∈ dyadicIntegers L,
        Metric.ball (rotate (gridRotation (angularWidth n) b)
          (LinearTransport.circularFrequency (FourierLocalization.coneFrequency K L k l))) e ⊆
            GuthMaldague.cap n θ := by
    by_cases hk : k ∈ dyadicIntegers K
    · have hk' := dyadic_bounds K k hk
      have ht := NeighborCount.sqrt_parameter_bounds hK hk'.1 hk'.2
      obtain ⟨b,i,hi⟩ := rotated_ball_subset_cap n (Real.sqrt ((k:ℝ)/K)) e ht.1
        (by nlinarith [ht.2.2]) he heu hδ hsmall hcone
      refine ⟨b,i,fun _ l hl => ?_⟩
      have hl' := dyadic_bounds L l hl
      rw [circularFrequency_generator K L hK hL k l hk'.1]
      exact hi _ ((le_div_iff₀ hL).mpr (by linarith)) ((div_lt_iff₀ hL).mpr hl'.2)
    · exact ⟨false,⟨0,by positivity⟩,fun hh => (hk hh).elim⟩
  choose b θ hh using hall
  exact ⟨b,θ,hh⟩

/-- The precise sharp projection for a ray assignment: the retained finite
sum is defined by the actual canonical cap index. -/
theorem sharpProjection_assigned_caps {ι : Type*} (I : Finset ι)
    (n : ℕ) (θ : ι → GuthMaldague.CapIndex n) (ξ : ι → Space) (e : ℝ)
    (hball : ∀ p ∈ I, Metric.ball (ξ p) e ⊆ GuthMaldague.cap n (θ p))
    (w : Space → ℂ) (hwc : Continuous w) (hwi : Integrable w)
    (hwF : Integrable (FourierTransform.fourier w))
    (hws : Function.support (FourierTransform.fourier w) ⊆ Metric.ball 0 e)
    (a : ι → ℂ) (i : GuthMaldague.CapIndex n) :
    GuthMaldague.capFunction n i (fun x => ∑ p ∈ I, a p*(w x*FourierLocalization.character (ξ p) x)) =
      fun x => ∑ p ∈ I.filter (fun p => θ p = i), a p*(w x*FourierLocalization.character (ξ p) x) := by
  classical
  apply FourierLocalization.sharpProjection_modulated_sum I _ (Finset.filter_subset _ I)
    a ξ w hwc hwi hwF e hws (GuthMaldague.cap n i)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,heq⟩
    simpa only [heq] using hball p hp
  · intro p hp hn
    have hne : θ p ≠ i := by simpa [hp] using hn
    exact (cap_disjoint n hne).mono_left (hball p hp)

theorem small_atom_conditions (n : ℕ) (hn : 5 ≤ n) (P c : ℝ) (hP : 0 < P)
    (hR : GuthMaldague.radius n < 4*P) (hc : 0 ≤ c) (hcu : c ≤ 1/256) :
    0 ≤ c/P ∧ c/P ≤ 1/4 ∧ angularWidth n ≤ 1/4 ∧
      12*(c/P) < angularWidth n/8 ∧ c/P < GuthMaldague.scale n^2 := by
  have hs := GuthMaldague.scale_pos n
  have hr := GuthMaldague.radius_pos n
  have hpow : (32:ℝ) ≤ 2^n := by
    calc
      _ = (2:ℝ)^5 := by norm_num
      _ ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
  have hsu : GuthMaldague.scale n ≤ 1/32 := by
    unfold GuthMaldague.scale
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 32) hpow
  have he : c/P ≤ (1/64)*GuthMaldague.scale n^2 := by
    rw [GuthMaldague.scale_sq_eq_radius_inv]
    have hb : c/P ≤ 1/(64*GuthMaldague.radius n) := by
      apply (div_le_div_iff₀ hP (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hcu hr.le]
    convert hb using 1 <;> ring
  refine ⟨div_nonneg hc hP.le, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · unfold angularWidth
    nlinarith [Real.pi_lt_four,Real.pi_pos]
  · unfold angularWidth
    nlinarith [Real.pi_gt_three, mul_nonneg (by linarith : 0 ≤ 1-GuthMaldague.scale n) hs.le]
  · nlinarith [sq_pos_of_pos hs]

theorem generator_rotated_angle (ρ r t : ℝ) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1)
    (hr : 0 < r) (ht : 1 ≤ t) (htu : t^2 ≤ 2) :
    GuthMaldague.cylindricalAngle (rotate ρ (generator r t)) = rayAngle t+ρ := by
  have hn : complexXY (generator r t) ≠ 0 := by
    intro hh
    have hp : 0 < (complexXY (generator r t)).re := by rw [complexXY_re]; change 0 < (3/5)*r*t; positivity
    simpa [hh] using hp
  have ha := generator_angle r t hr (by linarith)
  have hb := rayAngle_bounds t ht htu
  rw [rotated_angle ρ _ hn hρ hρu (by rw [ha]; linarith) (by rw [ha]; linarith),ha]

theorem same_cap_index_diameter (n : ℕ) (i : GuthMaldague.CapIndex n)
    (ρ K k j r r' : ℝ) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1) (hK : 0 < K)
    (hk : K ≤ k) (hku : k < 2*K) (hj : K ≤ j) (hju : j < 2*K)
    (hr : 0 < r) (hr' : 0 < r')
    (hki : rotate ρ (generator r (Real.sqrt (k/K))) ∈ GuthMaldague.cap n i)
    (hji : rotate ρ (generator r' (Real.sqrt (j/K))) ∈ GuthMaldague.cap n i) :
    |k-j| ≤ 16*K*angularWidth n := by
  have hkp := NeighborCount.sqrt_parameter_bounds hK hk hku
  have hjp := NeighborCount.sqrt_parameter_bounds hK hj hju
  have h1 := hki.2
  have h2 := hji.2
  rw [Set.mem_preimage, generator_rotated_angle ρ r _ hρ hρu hr hkp.1 (by nlinarith [hkp.2.2])] at h1
  rw [Set.mem_preimage, generator_rotated_angle ρ r' _ hρ hρu hr' hjp.1 (by nlinarith [hjp.2.2])] at h2
  have ha : |rayAngle (Real.sqrt (k/K))-rayAngle (Real.sqrt (j/K))| ≤ angularWidth n := by
    rcases h1 with ⟨h1,h1'⟩
    rcases h2 with ⟨h2,h2'⟩
    change _ < GuthMaldague.leftEndpoint n i+angularWidth n at h1'
    change _ < GuthMaldague.leftEndpoint n i+angularWidth n at h2'
    rw [abs_le]
    constructor <;> linarith
  exact (index_angle_separation K k j hK hk hku hj hju).trans
    (mul_le_mul_of_nonneg_left ha (by positivity))

end
end CircleDivisor.EnergyV3.AngularAtoms
