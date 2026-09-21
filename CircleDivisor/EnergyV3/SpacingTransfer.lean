import CircleDivisor.EnergyV3.EndpointTransfer
import CircleDivisor.ExternalPeriodBridge

/-! Connect the actual cone integral to the actual arithmetic sieve factor.
The input `hmoment` is an explicitly displayed internal spacing bound, not
an external input or an axiom. The theorem supplies its complete substitution
into the source interface, including comparability of the integer scales. -/

namespace CircleDivisor.EnergyV3.SpacingTransfer
noncomputable section
open CircleDivisor.ExternalInterfaces CircleDivisor.Arithmetic
open EndpointTransfer
open scoped BigOperators

def exponents (q : ℝ) (i : Fin 4) : ℝ × ℝ :=
  ![(q/2,q/2), (1,2*q-5), (q-2,q-3), (3*q/4-2,5*q/4-2)] i

def monomial (K L q : ℝ) (i : Fin 4) : ℝ :=
  K ^ (exponents q i).1 * L ^ (exponents q i).2

theorem fourTerm_eq_sum (K L q : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    Arithmetic.fourTerm K L q = ∑ i : Fin 4, monomial K L q i := by
  simp [Arithmetic.fourTerm, monomial, exponents, Fin.sum_univ_succ,
    Real.mul_rpow hK hL]
  ring

theorem exponents_mem (q : ℝ) (i : Fin 4) :
    exponents q i ∈ ({(q/2,q/2), (1,2*q-5), (q-2,q-3),
      (3*q/4-2,5*q/4-2)} : Finset (ℝ × ℝ)) := by
  fin_cases i <;> simp [exponents]

theorem exponents_range {q : ℝ} (hq : 4 < q) (hqu : q ≤ 9/2) (i : Fin 4) :
    0 ≤ (exponents q i).1 ∧ 0 ≤ (exponents q i).2 ∧
    (exponents q i).1 + (exponents q i).2 ≤ 5 := by
  fin_cases i <;> dsimp [exponents] <;>
    exact ⟨by linarith, by linarith, by linarith⟩

theorem monomial_compare {D K L K₀ L₀ q : ℝ} (hD : 1 ≤ D)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hK₀ : 0 ≤ K₀) (hL₀ : 0 ≤ L₀)
    (hKK : K ≤ D * K₀) (hLL : L ≤ D * L₀)
    (hq : 4 < q) (hqu : q ≤ 9/2) (i : Fin 4) :
    monomial K L q i ≤ D ^ (5 : ℝ) * monomial K₀ L₀ q i := by
  have hDp : 0 < D := by linarith
  have he := exponents_range hq hqu i
  unfold monomial
  calc
    _ ≤ (D*K₀)^(exponents q i).1 * (D*L₀)^(exponents q i).2 := by
      exact mul_le_mul (Real.rpow_le_rpow hK hKK he.1)
        (Real.rpow_le_rpow hL hLL he.2.1) (by positivity) (by positivity)
    _ = D^((exponents q i).1 + (exponents q i).2) *
        (K₀^(exponents q i).1 * L₀^(exponents q i).2) := by
      rw [Real.mul_rpow hDp.le hK₀, Real.mul_rpow hDp.le hL₀,
        Real.rpow_add hDp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hD he.2.2) (by positivity)

theorem fourTerm_compare {D K L K₀ L₀ q : ℝ} (hD : 1 ≤ D)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hK₀ : 0 ≤ K₀) (hL₀ : 0 ≤ L₀)
    (hKK : K ≤ D * K₀) (hLL : L ≤ D * L₀)
    (hq : 4 < q) (hqu : q ≤ 9/2) :
    Arithmetic.fourTerm K L q ≤ D ^ (5 : ℝ) * Arithmetic.fourTerm K₀ L₀ q := by
  rw [fourTerm_eq_sum K L q hK hL, fourTerm_eq_sum K₀ L₀ q hK₀ hL₀,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => monomial_compare hD hK hL hK₀ hL₀ hKK hLL hq hqu i

theorem rpow_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {p : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hp0 : p ≠ 0) :
    (∑ i ∈ s, f i)^p ≤ ∑ i ∈ s, (f i)^p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp0]
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      refine (Real.rpow_add_le_add_rpow (hf i (Finset.mem_insert_self _ _))
        (Finset.sum_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj))) hp hp1).trans ?_
      exact add_le_add_right (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) _

theorem root_fourTerm_sieve_le {H M N R Q q : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hq : 4 < q) :
    sieveFactor H M N R Q q *
      ((Q/R)^2 * Arithmetic.fourTerm (N*Q/R^2) (H*Q/R^2) q)^(1/q) ≤
    ∑ i : Fin 4, sieveMonomial H M N R Q q (exponents q i).1 (exponents q i).2 := by
  have hqp : 0 < q := by linarith
  have hsf : 0 ≤ sieveFactor H M N R Q q := by unfold sieveFactor; positivity
  rw [fourTerm_eq_sum _ _ _ (by positivity) (by positivity), Finset.mul_sum]
  have hs := rpow_sum_le Finset.univ
    (fun i : Fin 4 => (Q/R)^2 * monomial (N*Q/R^2) (H*Q/R^2) q i)
    (p := 1/q) (by intro i hi; unfold monomial; positivity) (by positivity)
    ((div_le_one hqp).2 (by linarith)) (ne_of_gt (by positivity))
  have hm := mul_le_mul_of_nonneg_left hs hsf
  rw [Finset.mul_sum] at hm
  exact hm

/-- Substitute a displayed internal moment estimate into the actual source
norm. The integer K,L and the eta interval keep all comparison factors. -/
theorem moment_contribution_bound {D H M N R Q η q C : ℝ} {K L : ℕ}
    (hD : 1 ≤ D) (hH : 0 < H) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hq : 4 < q) (hqu : q ≤ 9/2) (hC : 0 ≤ C)
    (p : SpacingParameters D H N R Q K L η) (a : ℤ → ℤ → ℂ)
    (hmoment : coneMoment K L q a ≤ C * Arithmetic.fourTerm K L q) :
    sieveFactor H M N R Q q * (etaSourceMoment K L η q a)^(1/q) ≤
      (C * D^6)^(1/q) *
        ∑ i : Fin 4, sieveMonomial H M N R Q q (exponents q i).1 (exponents q i).2 := by
  have hqp : 0 < q := by linarith
  have hDp : 0 < D := by linarith
  have hηp : 0 < η := p.eta_pos
  have hsf : 0 ≤ sieveFactor H M N R Q q := by unfold sieveFactor; positivity
  have hfour : 0 ≤ Arithmetic.fourTerm (N*Q/R^2) (H*Q/R^2) q := by
    unfold Arithmetic.fourTerm
    positivity
  have hc := fourTerm_compare hD (show 0 ≤ (K:ℝ) by positivity)
    (show 0 ≤ (L:ℝ) by positivity) (by positivity) (by positivity)
    p.K_comparable.2 p.L_comparable.2 hq hqu
  have hη := ExternalPeriodBridge.etaSourceMoment_le_of_spacingParameters p
    (show 0 ≤ q by linarith) a
  have hraw : etaSourceMoment K L η q a ≤
      (C*D^6) * ((Q/R)^2 * Arithmetic.fourTerm (N*Q/R^2) (H*Q/R^2) q) := by
    calc
      _ ≤ (η*K*L) * coneMoment K L q a := hη
      _ ≤ (η*K*L) * (C * Arithmetic.fourTerm K L q) := by
        exact mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ ≤ (D*(Q/R)^2) * (C*(D^(5:ℝ) * Arithmetic.fourTerm (N*Q/R^2) (H*Q/R^2) q)) := by
        apply mul_le_mul p.eta_product_comparable.2
          (mul_le_mul_of_nonneg_left hc hC) _ (by positivity)
        unfold Arithmetic.fourTerm
        positivity
      _ = _ := by rw [show D^(5:ℝ)=D^(5:ℕ) from Real.rpow_natCast D 5]; ring
  have hp := Real.rpow_le_rpow
    (etaSourceMoment_nonneg (by positivity) (by positivity) p.eta_pos.le a)
    hraw (show 0 ≤ 1/q by positivity)
  calc
    _ ≤ sieveFactor H M N R Q q *
        ((C*D^6) * ((Q/R)^2 * Arithmetic.fourTerm (N*Q/R^2) (H*Q/R^2) q))^(1/q) :=
      mul_le_mul_of_nonneg_left hp hsf
    _ = (C*D^6)^(1/q) * (sieveFactor H M N R Q q *
        ((Q/R)^2 * Arithmetic.fourTerm (N*Q/R^2) (H*Q/R^2) q)^(1/q)) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (root_fourTerm_sieve_le hH hM hN hR hQ hq) (by positivity)

/-- The full arithmetic contribution after the revised spacing substitution:
every internal denominator and block-length comparison is discharged. -/
theorem actual_moment_contribution_bound {D T h m ell n N R Q η C : ℝ} {K L : ℕ}
    (hD : 1 ≤ D) (hT : 1 < T) (hN : 0 < N) (hR : 0 < R)
    (hNl : T^n/D ≤ N) (hRl : T^radiusExponent m n/D ≤ R)
    (hr : HardRange theta h m) (hell : 0 ≤ ell) (hn : blockA h m ell ≤ n)
    (hQ : R ≤ Q) (hC : 0 ≤ C)
    (p : SpacingParameters D (T^h) N R Q K L η) (a : ℤ → ℤ → ℂ)
    (hmoment : coneMoment K L (qHat (h-m)) a ≤
      C * Arithmetic.fourTerm K L (qHat (h-m))) :
    sieveFactor (T^h) (T^m) N R Q (qHat (h-m)) *
      (etaSourceMoment K L η (qHat (h-m)) a)^(1/qHat (h-m)) ≤
        4 * (C*D^6)^(1/qHat (h-m)) * D^2 * T^(h+theta) := by
  have ht : 0 < T := by linarith
  have hq := qHat_range (h-m)
  have hb := moment_contribution_bound (M := T^m) hD (by positivity) (by positivity) hN hR
    (hR.trans_le hQ) hq.1 hq.2 hC p a hmoment
  have hs : (∑ i : Fin 4, sieveMonomial (T^h) (T^m) N R Q (qHat (h-m))
      (exponents (qHat (h-m)) i).1 (exponents (qHat (h-m)) i).2) ≤
      4 * (D^2 * T^(h+theta)) := by
    calc
      _ ≤ ∑ i : Fin 4, D^2*T^(h+theta) := Finset.sum_le_sum fun i hi =>
        actual_sieveMonomial_bound hD hT hN hR hNl hRl hr hell hn hQ
          (by simpa only [Prod.mk.eta] using exponents_mem (qHat (h-m)) i)
      _ = _ := by simp
  calc
    _ ≤ _ := hb
    _ ≤ (C*D^6)^(1/qHat (h-m)) * (4 * (D^2 * T^(h+theta))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end
end CircleDivisor.EnergyV3.SpacingTransfer
