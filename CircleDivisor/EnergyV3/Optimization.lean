import Mathlib

/-! Exact optimization for the September 8 energy manuscript. Every statement
here is an unconditional theorem of real arithmetic; no spacing estimate is
assumed. The four fixed moments avoid any uniformity assumption in Li--Yang. -/

namespace CircleDivisor.EnergyV3
noncomputable section

def theta : ℝ := 573 / 1828
def hardInterval (x : ℝ) : Prop := 2 * theta - 1 < x ∧ x ≤ -theta
def kappa (x : ℝ) : ℝ := -47 / 200 - 24 * x / 25
def lam (x : ℝ) : ℝ := 51 / 200 + 17 * x / 25
def E (x q : ℝ) : ℝ := (-9 / 50 + 22 / (25 * q)) * x +
  49 / 200 + 33 / (100 * q)
def qHat (x : ℝ) : ℝ :=
  if x ≤ -101 / 286 then 201 / 50 else
  if x ≤ -251 / 736 then 17 / 4 else
  if x ≤ -1 / 3 then 22 / 5 else 9 / 2
def qChoice (x : ℝ) : ℝ :=
  if x ≤ -1 / 3 then (59 + 24 * x) / (2 - 28 * x) else 9 / 2
def ELeft (x : ℝ) : ℝ := -(5792 * x ^ 2 + 2444 * x - 3023) /
  (200 * (24 * x + 59))

theorem theta_margins :
    theta - 49 / 164 = 275 / 18737 ∧
    theta - 4 / 13 = 137 / 23764 ∧
    theta - 253 / 808 = 125 / 369256 ∧
    theta - 5 / 16 = 7 / 7312 ∧
    theta - 89 / 284 = 5 / 64894 ∧
    theta - 47 / 150 = 17 / 137100 := by
  norm_num [theta]

theorem theta_bounds : 1 / 4 < theta ∧ theta < 1 / 3 := by norm_num [theta]

theorem breakpoints_increasing :
    2 * theta - 1 < -101 / 286 ∧
    (-101 : ℝ) / 286 < -251 / 736 ∧
    (-251 : ℝ) / 736 < -1 / 3 ∧ (-1 : ℝ) / 3 < -theta := by
  norm_num [theta]

theorem hardInterval_basic {x : ℝ} (hx : hardInterval x) :
    0 < lam x ∧ lam x ≤ kappa x ∧ 0 < kappa x := by
  dsimp [hardInterval, theta] at hx
  dsimp [lam, kappa]
  exact ⟨by linarith [hx.1], by linarith [hx.2], by linarith [hx.2]⟩

theorem qHat_mem (x : ℝ) :
    qHat x ∈ ({201 / 50, 17 / 4, 22 / 5, 9 / 2} : Finset ℝ) := by
  unfold qHat
  split_ifs <;> simp

theorem qHat_range (x : ℝ) : 4 < qHat x ∧ qHat x ≤ 9 / 2 := by
  unfold qHat
  split_ifs <;> norm_num

/-- This checks both spacing inequalities and the final exponent on every
point of the full hard interval, using only four fixed moments. -/
theorem four_moment_optimization {x : ℝ} (hx : hardInterval x) :
    (qHat x - 4) * kappa x ≤ (6 - qHat x) * lam x ∧
    (3 * qHat x - 8) * lam x ≤ (8 - qHat x) * kappa x ∧
    E x (qHat x) ≤ theta := by
  rcases hx with ⟨hl, hu⟩
  dsimp [theta] at hl hu ⊢
  unfold qHat
  split_ifs with h1 h2 h3
  all_goals norm_num [kappa, lam, E]
  all_goals constructor; · linarith
  all_goals constructor <;> linarith

theorem four_moment_equality_iff {x : ℝ} (hx : hardInterval x) :
    E x (qHat x) = theta ↔ x = -theta := by
  rcases hx with ⟨hl, hu⟩
  dsimp [theta] at hl hu ⊢
  unfold qHat
  split_ifs with h1 h2 h3
  all_goals norm_num [E]
  all_goals constructor <;> intro h <;> linarith

theorem four_endpoint_values :
    E (-101 / 286) (201 / 50) = 72053 / 229944 ∧
    E (-251 / 736) (17 / 4) = 341 / 1088 ∧
    E (-1 / 3) (22 / 5) = 47 / 150 ∧
    E (-theta) (9 / 2) = theta := by norm_num [E, theta]

theorem four_endpoint_margins :
    theta - E (-101 / 286) (201 / 50) = 11257 / 105084408 ∧
    theta - E (-251 / 736) (17 / 4) = 19 / 497216 ∧
    theta - E (-1 / 3) (22 / 5) = 17 / 137100 ∧
    theta - E (-theta) (9 / 2) = 0 := by norm_num [E, theta]

theorem positive_square (x : ℝ) :
    17376 * x ^ 2 + 11844 * x + 2023 =
      17376 * (x + 987 / 2896) ^ 2 + 6797 / 1448 := by ring

theorem rational_certificate (x : ℝ) (hx : 24 * x + 59 ≠ 0) :
    47 / 150 - ELeft x =
      (17376 * x ^ 2 + 11844 * x + 2023) / (600 * (24 * x + 59)) := by
  unfold ELeft
  have hx' : 59 + x * 24 ≠ 0 := by
    intro h
    apply hx
    linarith
  field_simp [hx, hx']
  ring_nf
  field_simp [hx']
  <;> ring

theorem left_exponent_strict {x : ℝ} (hx : hardInterval x) :
    ELeft x < 47 / 150 ∧ (47 : ℝ) / 150 < theta := by
  have hd : 0 < 24 * x + 59 := by
    have hl := hx.1
    dsimp [theta] at hl
    linarith
  have hn : 0 < 17376 * x ^ 2 + 11844 * x + 2023 := by
    rw [positive_square]
    positivity
  have he := rational_certificate x (ne_of_gt hd)
  have hp := div_pos hn (mul_pos (by norm_num : (0 : ℝ) < 600) hd)
  exact ⟨by linarith, by norm_num [theta]⟩

end
end CircleDivisor.EnergyV3
