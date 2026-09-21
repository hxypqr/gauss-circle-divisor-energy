import CircleDivisor.EnergyV3.AngularAtoms

namespace CircleDivisor.EnergyV3.CapNesting
open Finset
noncomputable section

theorem scale_mono {j n : ℕ} (hjn : j ≤ n) : GuthMaldague.scale n ≤ GuthMaldague.scale j := by
  unfold GuthMaldague.scale
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hjn)

theorem scale_factor {j n : ℕ} (hjn : j ≤ n) :
    GuthMaldague.scale j = (2:ℝ)^(n-j)*GuthMaldague.scale n := by
  have hp : (2:ℝ)^n = (2:ℝ)^j*(2:ℝ)^(n-j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
  unfold GuthMaldague.scale
  rw [hp]
  field_simp

/-- Every fine canonical cap is contained in a canonical coarse cap, including
the actual cone-neighborhood part of the definition. -/
theorem exists_parent (n j : ℕ) (hjn : j ≤ n) (i : GuthMaldague.CapIndex n) :
    ∃ m : GuthMaldague.CapIndex j, GuthMaldague.cap n i ⊆ GuthMaldague.cap j m := by
  let d : ℕ := 2^(n-j)
  have hd : 0 < d := by dsimp [d]; positivity
  have hp : 2^n = 2^j*d := by dsimp [d]; rw [← pow_add, Nat.add_sub_of_le hjn]
  have him : i.val/d < 2^j := (Nat.div_lt_iff_lt_mul hd).mpr (by rw [← hp]; exact i.isLt)
  let m : GuthMaldague.CapIndex j := ⟨i.val/d,him⟩
  refine ⟨m,fun ξ hξ => ?_⟩
  refine ⟨?_,?_⟩
  · obtain ⟨η,hη,hnear⟩ := hξ.1
    exact ⟨η,hη,hnear.trans_le (pow_le_pow_left₀ (GuthMaldague.scale_pos n).le (scale_mono hjn) 2)⟩
  · have hlo : (m.val:ℝ)*(d:ℝ) ≤ (i.val:ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self i.val d)
    have hhi : (i.val:ℝ)+1 ≤ ((m.val:ℝ)+1)*(d:ℝ) := by
      have hh : i.val < (i.val/d+1)*d := by
        have hmod := Nat.mod_lt i.val hd
        have heq := Nat.mod_add_div i.val d
        nlinarith
      exact_mod_cast (show i.val+1 ≤ (m.val+1)*d by dsimp [m]; omega)
    have hs := GuthMaldague.scale_pos n
    have hf : GuthMaldague.scale j = (d:ℝ)*GuthMaldague.scale n := by
      simpa [d] using scale_factor hjn
    have hl := hξ.2.1
    have hu := hξ.2.2
    change GuthMaldague.leftEndpoint n i ≤ GuthMaldague.cylindricalAngle ξ at hl
    change GuthMaldague.cylindricalAngle ξ < GuthMaldague.leftEndpoint n i+2*Real.pi*GuthMaldague.scale n at hu
    change GuthMaldague.leftEndpoint j m ≤ GuthMaldague.cylindricalAngle ξ ∧
      GuthMaldague.cylindricalAngle ξ < GuthMaldague.leftEndpoint j m+2*Real.pi*GuthMaldague.scale j
    unfold GuthMaldague.leftEndpoint at *
    rw [hf]
    have hπ := Real.pi_pos
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2*Real.pi*GuthMaldague.scale n)]
    · nlinarith [mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 2*Real.pi*GuthMaldague.scale n)]

theorem exists_fineChild_parent (n j : ℕ) (hjn : j ≤ n) (i : GuthMaldague.CapIndex n) :
    ∃ m : GuthMaldague.CapIndex j, i ∈ GuthMaldague.fineChildren n j m := by
  obtain ⟨m,hm⟩ := exists_parent n j hjn i
  exact ⟨m,by simp [GuthMaldague.fineChildren,hm]⟩

theorem fineChild_parent_unique (n j : ℕ) (i : GuthMaldague.CapIndex n)
    (hi : (GuthMaldague.cap n i).Nonempty) {a b : GuthMaldague.CapIndex j}
    (ha : i ∈ GuthMaldague.fineChildren n j a) (hb : i ∈ GuthMaldague.fineChildren n j b) : a=b := by
  obtain ⟨ξ,hξ⟩ := hi
  have hsa : GuthMaldague.cap n i ⊆ GuthMaldague.cap j a := by simpa [GuthMaldague.fineChildren] using ha
  have hsb : GuthMaldague.cap n i ⊆ GuthMaldague.cap j b := by simpa [GuthMaldague.fineChildren] using hb
  by_contra hn
  exact Set.disjoint_left.mp (AngularAtoms.cap_disjoint j hn) (hsa hξ) (hsb hξ)

def coarsePoints {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (n j : ℕ) (θ : ι → GuthMaldague.CapIndex n) (a : GuthMaldague.CapIndex j) : Finset ι :=
  I.filter (fun p => θ p ∈ GuthMaldague.fineChildren n j a)

theorem coarsePoints_disjoint {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (n j : ℕ) (θ : ι → GuthMaldague.CapIndex n)
    (hθ : ∀ p ∈ I, (GuthMaldague.cap n (θ p)).Nonempty) :
    Pairwise (fun a b : GuthMaldague.CapIndex j => Disjoint (coarsePoints I n j θ a) (coarsePoints I n j θ b)) := by
  intro a b hn
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rcases Finset.mem_filter.mp hp with ⟨hp,hpa⟩
  rcases Finset.mem_filter.mp hq with ⟨_,hpb⟩
  exact hn (fineChild_parent_unique n j (θ p) (hθ p hp) hpa hpb)

theorem coarsePoints_union {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (n j : ℕ) (hjn : j ≤ n) (θ : ι → GuthMaldague.CapIndex n) :
    Finset.univ.biUnion (coarsePoints I n j θ) = I := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, coarsePoints, Finset.mem_filter]
  constructor
  · rintro ⟨_,hp,_⟩; exact hp
  · intro hp
    obtain ⟨a,ha⟩ := exists_fineChild_parent n j hjn (θ p)
    exact ⟨a,hp,ha⟩

end
end CircleDivisor.EnergyV3.CapNesting
