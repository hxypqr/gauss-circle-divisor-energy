import CircleDivisor.EnergyV3.Arithmetic

/-! The exponent calculations are connected here to the actual real-power
expressions in the arithmetic interface. These are unconditional inequalities
for each of its four monomial contributions. -/

namespace CircleDivisor.EnergyV3.EndpointTransfer
noncomputable section
open CircleDivisor.Arithmetic CircleDivisor.ExternalInterfaces

/-- A complete monomial contribution after the smaller-box comparison and
the qth root. Its dependence on the denominator Q is retained explicitly. -/
def sieveMonomial (H M N R Q q a b : ℝ) : ℝ :=
  sieveFactor H M N R Q q *
    ((Q / R) ^ 2 * ((N * Q / R ^ 2) ^ a * (H * Q / R ^ 2) ^ b)) ^ (1 / q)

theorem sieveMonomial_pos {H M N R Q q a b : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q) :
    0 < sieveMonomial H M N R Q q a b := by
  unfold sieveMonomial sieveFactor
  positivity

theorem log_sieveMonomial {H M N R Q q a b : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hq : q ≠ 0) :
    Real.log (sieveMonomial H M N R Q q a b) =
      Real.log M + Real.log R - Real.log N +
      22 / (17 * q) * (Real.log H - Real.log R) +
      (a * (Real.log N - Real.log R) + b * (Real.log H - Real.log R)) / q +
      denominatorPower q a b / q * (Real.log Q - Real.log R) := by
  unfold sieveMonomial sieveFactor
  repeat first
    | rw [Real.log_mul (by positivity) (by positivity)]
    | rw [Real.log_div (by positivity) (by positivity)]
    | rw [Real.log_rpow (by positivity)]
    | rw [Real.log_pow]
  unfold denominatorPower
  field_simp
  ring

/-- Denominator monotonicity is proved for the complete actual expression,
not for a square-root replacement at larger Q. -/
theorem sieveMonomial_le_endpoint {H M N R Q q a b : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRQ : R ≤ Q) (hq : 0 < q) (hp : denominatorPower q a b ≤ 0) :
    sieveMonomial H M N R Q q a b ≤ sieveMonomial H M N R R q a b := by
  have hQ : 0 < Q := hR.trans_le hRQ
  apply (Real.log_le_log_iff (sieveMonomial_pos hH hM hN hR hQ)
    (sieveMonomial_pos hH hM hN hR hR)).mp
  rw [log_sieveMonomial hH hM hN hR hQ (ne_of_gt hq),
    log_sieveMonomial hH hM hN hR hR (ne_of_gt hq)]
  have hrq : 0 ≤ Real.log Q - Real.log R :=
    sub_nonneg.mpr ((Real.log_le_log_iff hR hQ).2 hRQ)
  have hs := mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hp hq.le) hrq
  linarith

theorem log_sieveMonomial_powers (T h m n q a b : ℝ) (hT : 0 < T) (hq : q ≠ 0) :
    Real.log (sieveMonomial (T ^ h) (T ^ m) (T ^ n)
      (T ^ radiusExponent m n) (T ^ radiusExponent m n) q a b) =
    endpointExponent q a b h m n * Real.log T := by
  rw [log_sieveMonomial (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hq]
  simp only [Real.log_rpow hT, sub_self, mul_zero, add_zero]
  dsimp [endpointExponent, lExponent, kExponent]
  ring

theorem sieveMonomial_powers (T h m n q a b : ℝ) (hT : 0 < T) (hq : q ≠ 0) :
    sieveMonomial (T ^ h) (T ^ m) (T ^ n)
      (T ^ radiusExponent m n) (T ^ radiusExponent m n) q a b =
    T ^ endpointExponent q a b h m n := by
  have hp : 0 < sieveMonomial (T ^ h) (T ^ m) (T ^ n)
      (T ^ radiusExponent m n) (T ^ radiusExponent m n) q a b :=
    sieveMonomial_pos (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity)
  have ht := Real.rpow_pos_of_pos hT (endpointExponent q a b h m n)
  apply le_antisymm
  · apply (Real.log_le_log_iff hp ht).mp
    rw [log_sieveMonomial_powers T h m n q a b hT hq, Real.log_rpow hT]
  · apply (Real.log_le_log_iff ht hp).mp
    rw [log_sieveMonomial_powers T h m n q a b hT hq, Real.log_rpow hT]

/-- Turn an endpoint exponent bound into an actual real-power bound at every
admissible denominator, with no analytic estimate hidden in the premises. -/
theorem sieveMonomial_le_power {T h m n q a b Q z : ℝ} (hT : 1 < T)
    (hQ : T ^ radiusExponent m n ≤ Q) (hq : 0 < q)
    (hp : denominatorPower q a b ≤ 0) (he : endpointExponent q a b h m n ≤ z) :
    sieveMonomial (T ^ h) (T ^ m) (T ^ n) (T ^ radiusExponent m n) Q q a b ≤ T ^ z := by
  have ht : 0 < T := by linarith
  calc
    _ ≤ sieveMonomial (T ^ h) (T ^ m) (T ^ n) (T ^ radiusExponent m n)
        (T ^ radiusExponent m n) q a b :=
      sieveMonomial_le_endpoint (by positivity) (by positivity) (by positivity)
        (by positivity) hQ hq hp
    _ = T ^ endpointExponent q a b h m n :=
      sieveMonomial_powers T h m n q a b ht (ne_of_gt hq)
    _ ≤ T ^ z := Real.rpow_le_rpow_of_exponent_le hT.le he

theorem four_sieveMonomial_bounds {T h m ell n Q : ℝ} (hT : 1 < T)
    (hr : HardRange theta h m) (hell : 0 ≤ ell) (hn : blockA h m ell ≤ n)
    (hQ : T ^ radiusExponent m n ≤ Q) :
    sieveMonomial (T ^ h) (T ^ m) (T ^ n) (T ^ radiusExponent m n) Q
      (qHat (h-m)) (qHat (h-m) / 2) (qHat (h-m) / 2) ≤ T ^ (h + theta) ∧
    sieveMonomial (T ^ h) (T ^ m) (T ^ n) (T ^ radiusExponent m n) Q
      (qHat (h-m)) 1 (2 * qHat (h-m) - 5) ≤ T ^ (h + theta) ∧
    sieveMonomial (T ^ h) (T ^ m) (T ^ n) (T ^ radiusExponent m n) Q
      (qHat (h-m)) (qHat (h-m) - 2) (qHat (h-m) - 3) ≤ T ^ (h + theta) ∧
    sieveMonomial (T ^ h) (T ^ m) (T ^ n) (T ^ radiusExponent m n) Q
      (qHat (h-m)) (3 * qHat (h-m) / 4 - 2) (5 * qHat (h-m) / 4 - 2)
      ≤ T ^ (h + theta) := by
  have hq := qHat_range (h-m)
  have hp := Arithmetic.denominator_powers (qHat (h-m))
  have hs := Arithmetic.denominator_powers_negative hq.1
  have he := Arithmetic.four_actual_endpoint_bounds hr hell hn
  refine ⟨sieveMonomial_le_power hT hQ (by linarith) ?_ he.1,
    sieveMonomial_le_power hT hQ (by linarith) ?_ he.2.1,
    sieveMonomial_le_power hT hQ (by linarith) ?_ he.2.2.1,
    sieveMonomial_le_power hT hQ (by linarith) ?_ he.2.2.2⟩
  · rw [hp.1]; exact hs.1.le
  · rw [hp.2.1]; exact hs.2.1.le
  · rw [hp.2.2.1]; exact hs.2.2.le
  · rw [hp.2.2.2]; exact hs.2.1.le

private theorem coefficient_error {D u v c : ℝ} (hD : 0 ≤ D)
    (hlo : -D ≤ u-v) (hc0 : -1 ≤ c) (hc1 : c ≤ 0) : c * (u-v) ≤ D := by
  have h1 := mul_le_mul_of_nonpos_left hlo hc1
  have h2 := mul_le_mul_of_nonneg_right hc0 hD
  nlinarith

/-- The two independent comparison errors in the actual integer N and the
arithmetic radius cost at most D², uniformly over all four moments. -/
theorem endpoint_comparable {D H M N N₀ R R₀ q a b : ℝ}
    (hD : 1 ≤ D) (hH : 0 < H) (hM : 0 < M)
    (hN : 0 < N) (hN₀ : 0 < N₀) (hR : 0 < R) (hR₀ : 0 < R₀)
    (hNl : N₀ / D ≤ N) (hRl : R₀ / D ≤ R) (hq : q ≠ 0)
    (ha : -1 ≤ -1 + a / q ∧ -1 + a / q ≤ 0)
    (hab : -1 ≤ 1 - 22 / (17*q) - (a+b)/q ∧
      1 - 22 / (17*q) - (a+b)/q ≤ 0) :
    sieveMonomial H M N R R q a b ≤ D ^ 2 * sieveMonomial H M N₀ R₀ R₀ q a b := by
  have hDp : 0 < D := by linarith
  have hDl : 0 ≤ Real.log D := Real.log_nonneg hD
  have hNl' := (Real.log_le_log_iff (div_pos hN₀ hDp) hN).2 hNl
  have hRl' := (Real.log_le_log_iff (div_pos hR₀ hDp) hR).2 hRl
  rw [Real.log_div (ne_of_gt hN₀) (ne_of_gt hDp)] at hNl'
  rw [Real.log_div (ne_of_gt hR₀) (ne_of_gt hDp)] at hRl'
  have heN := coefficient_error hDl (show -Real.log D ≤ Real.log N - Real.log N₀ by linarith)
    ha.1 ha.2
  have heR := coefficient_error hDl (show -Real.log D ≤ Real.log R - Real.log R₀ by linarith)
    hab.1 hab.2
  apply (Real.log_le_log_iff (sieveMonomial_pos hH hM hN hR hR)
    (mul_pos (pow_pos hDp 2) (sieveMonomial_pos hH hM hN₀ hR₀ hR₀))).mp
  rw [Real.log_mul (by positivity) (ne_of_gt (sieveMonomial_pos hH hM hN₀ hR₀ hR₀)),
    Real.log_pow, log_sieveMonomial hH hM hN hR hR hq,
    log_sieveMonomial hH hM hN₀ hR₀ hR₀ hq]
  simp only [add_div, sub_div, div_eq_mul_inv, sub_self, mul_zero, add_zero] at heN heR ⊢
  nlinarith

theorem four_coefficient_ranges {q : ℝ} (hq : 4 < q) (hqu : q ≤ 9/2) :
    (∀ (a b : ℝ), (a,b) ∈ ({(q/2,q/2), (1,2*q-5), (q-2,q-3),
      (3*q/4-2,5*q/4-2)} : Finset (ℝ × ℝ)) →
      (-1 ≤ -1+a/q ∧ -1+a/q ≤ 0) ∧
      (-1 ≤ 1-22/(17*q)-(a+b)/q ∧ 1-22/(17*q)-(a+b)/q ≤ 0)) := by
  have hqp : 0 < q := by linarith
  intro a b hab
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hab
  rcases hab with h | h | h | h
  all_goals rcases h with ⟨rfl,rfl⟩
  all_goals constructor <;> constructor
  all_goals field_simp
  all_goals nlinarith

/-- Final internal contribution bound with the actual rounded block length
and radius. Constants, Q variation, and all four complete monomials are
handled before any square-root comparison is made. -/
theorem actual_sieveMonomial_bound {D T h m ell n N R Q a b : ℝ}
    (hD : 1 ≤ D) (hT : 1 < T) (hN : 0 < N) (hR : 0 < R)
    (hNl : T ^ n / D ≤ N) (hRl : T ^ radiusExponent m n / D ≤ R)
    (hr : HardRange theta h m) (hell : 0 ≤ ell) (hn : blockA h m ell ≤ n)
    (hQ : R ≤ Q)
    (hab : (a,b) ∈ ({(qHat (h-m)/2,qHat (h-m)/2),
      (1,2*qHat (h-m)-5), (qHat (h-m)-2,qHat (h-m)-3),
      (3*qHat (h-m)/4-2,5*qHat (h-m)/4-2)} : Finset (ℝ × ℝ))) :
    sieveMonomial (T^h) (T^m) N R Q (qHat (h-m)) a b ≤ D^2 * T^(h+theta) := by
  have ht : 0 < T := by linarith
  have hq := qHat_range (h-m)
  have hc := four_coefficient_ranges hq.1 hq.2 a b hab
  have he := Arithmetic.four_actual_endpoint_bounds hr hell hn
  have hp : denominatorPower (qHat (h-m)) a b ≤ 0 := by
    have hd := Arithmetic.denominator_powers (qHat (h-m))
    have hs := Arithmetic.denominator_powers_negative hq.1
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hab
    rcases hab with hh | hh | hh | hh
    all_goals rcases hh with ⟨rfl,rfl⟩
    · rw [hd.1]; exact hs.1.le
    · rw [hd.2.1]; exact hs.2.1.le
    · rw [hd.2.2.1]; exact hs.2.2.le
    · rw [hd.2.2.2]; exact hs.2.1.le
  have he' : endpointExponent (qHat (h-m)) a b h m n ≤ h+theta := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hab
    rcases hab with hh | hh | hh | hh
    all_goals rcases hh with ⟨rfl,rfl⟩
    · exact he.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2
  calc
    _ ≤ sieveMonomial (T^h) (T^m) N R R (qHat (h-m)) a b :=
      sieveMonomial_le_endpoint (by positivity) (by positivity) hN hR hQ (by linarith) hp
    _ ≤ D^2 * sieveMonomial (T^h) (T^m) (T^n) (T^radiusExponent m n)
        (T^radiusExponent m n) (qHat (h-m)) a b :=
      endpoint_comparable hD (by positivity) (by positivity) hN (by positivity) hR
        (by positivity) hNl hRl (by linarith) hc.1 hc.2
    _ = D^2 * T^endpointExponent (qHat (h-m)) a b h m n := by
      rw [sieveMonomial_powers T h m n (qHat (h-m)) a b ht (by linarith)]
    _ ≤ D^2 * T^(h+theta) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT.le he') (sq_nonneg D)

end
end CircleDivisor.EnergyV3.EndpointTransfer
