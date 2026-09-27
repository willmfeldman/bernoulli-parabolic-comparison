/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.Data

/-!
# South-pole reduction

If `ν² = -e_t` then `ν¹ = e_t`; if `ν¹ = -e_t` then `ν² = e_t` (`south_reduction`).

Proof. If `ν² = -e_t`, the exterior centre `c₂ = p⋆ + μ ν²` is the dual centre `p̂`, so `v₁ = 0` on
`B̄_μ(p̂) ∩ D₁` (`Contact.exterior_ball`), while `B̄_μ(c₁) ∩ D₁ ⊆ E₁` (`Contact.interior_ball`) and
`E₁ ∩ {t < t⋆} ⊆ {v₁ > 0}` (`Contact.contact_structure_pos`). Since `B_μ(p̂) ⊆ D₁ ∩ {t < t⋆}`
(room), the balls `B_μ(p̂)` and `B̄_μ(c₁)` are disjoint. But `c₁ = p̂ + μ (e_t + ν¹)`, and for a
unit vector `ν¹ ≠ e_t` the point `p̂ + (μ/2)(e_t + ν¹)` lies in both
(`exists_mem_stBallOpen_inter_stBall`). The second claim is symmetric, with
`Contact.exterior_past` (no point of `E₁` before `t⋆` in the ball `B̄_μ(q₂ + μ e_t)`) in place of
`Contact.contact_structure_pos`.
-/

@[expose] public section

open Set

namespace BernoulliComparison

namespace Polar

open Crossing Config Contact

variable {d : ℕ}

/-- For a Euclidean unit vector `ν ≠ e_t`, the open ball `B_μ(c)` meets the closed ball
`B̄_μ(c + μ e_t + μ ν)`: the point `c + (μ/2)(ν + e_t)` lies in both. -/
theorem exists_mem_stBallOpen_inter_stBall {ν : E d × ℝ} (hν : ‖ν.1‖ ^ 2 + ν.2 ^ 2 = 1)
    (hne : ν ≠ ((0 : E d), (1 : ℝ))) {μ : ℝ} (hμ : 0 < μ) (c : E d × ℝ) :
    ∃ m, m ∈ stBallOpen c μ ∧ m ∈ stBall (c + ((0 : E d), μ) + μ • ν) μ := by
  have hlt : ν.2 < 1 := by
    have hle : ν.2 ≤ 1 := by nlinarith [sq_nonneg ‖ν.1‖, sq_nonneg (ν.2 - 1)]
    refine lt_of_le_of_ne hle fun h ↦ hne ?_
    have h0 : ‖ν.1‖ ^ 2 = 0 := by rw [h] at hν; linarith
    have h1 : ν.1 = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
    exact Prod.ext h1 h
  refine ⟨(c.1 + (μ / 2) • ν.1, c.2 + μ / 2 * (ν.2 + 1)), ?_, ?_⟩
  · rw [mem_stBallOpen]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hμ)]
    have key : (μ / 2 * ‖ν.1‖) ^ 2 + (μ / 2 * (ν.2 + 1)) ^ 2 = μ ^ 2 * ((1 + ν.2) / 2) := by
      linear_combination (μ ^ 2 / 4) * hν
    rw [key]
    exact mul_lt_of_lt_one_right (by positivity) (by linarith)
  · rw [mem_stBall]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, add_zero]
    have : c.1 + (μ / 2) • ν.1 - (c.1 + μ • ν.1) = (-(μ / 2)) • ν.1 := by
      rw [neg_smul, show μ = μ / 2 + μ / 2 by ring, add_smul]
      simp only [add_halves]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hμ)]
    nlinarith

variable {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset}

/-- `p⋆ = p̂ + μ e_t`. -/
theorem pstar_eq_phat_add (C : ContactData P) : C.pstar = C.phat + ((0 : E d), P.μ) := by
  rw [← C.pstar_sub_phat, add_sub_cancel]

/-- A centre `p⋆ + μ ν` with `ν = -e_t` is the dual centre `p̂`. -/
theorem pstar_add_south (C : ContactData P) :
    C.pstar + P.μ • ((0 : E d), (-1 : ℝ)) = C.phat := by
  rw [pstar_eq_phat_add]
  ext <;> simp

/-- Points of `B_μ(p̂)` lie in `D₁` and before `t⋆` (room). -/
theorem mem_D₁_of_mem_dualBallOpen (C : ContactData P) {m : E d × ℝ}
    (hm : m ∈ stBallOpen C.phat P.μ) : m ∈ P.D₁ ∧ m.2 < C.pstar.2 := by
  have h := C.dualBallOpen_subset_past hm
  exact ⟨prod_Ioc_subset_D₁ P h.1, h.2⟩

/-- South-pole reduction: if `ν² = -e_t` then `ν¹ = e_t`; if `ν¹ = -e_t` then
`ν² = e_t`. -/
theorem south_reduction (C : ContactData P) :
    (C.ν₂ = ((0 : E d), (-1 : ℝ)) → C.ν₁ = ((0 : E d), (1 : ℝ))) ∧
      (C.ν₁ = ((0 : E d), (-1 : ℝ)) → C.ν₂ = ((0 : E d), (1 : ℝ))) := by
  constructor
  · intro h2
    by_contra h1
    obtain ⟨m, hm, hm'⟩ := exists_mem_stBallOpen_inter_stBall C.ν₁_unit h1 P.μ_pos C.phat
    obtain ⟨hmD, hmt⟩ := mem_D₁_of_mem_dualBallOpen C hm
    have hc₁ : C.phat + ((0 : E d), P.μ) + P.μ • C.ν₁ = C.q₁ + ((0 : E d), P.μ) := by
      rw [← pstar_eq_phat_add, ← C.ctr₁_eq_pstar_add, ContactData.ctr₁]
    rw [hc₁] at hm'
    have hpos := C.v₁_pos_of_past m (C.interior_ball m hmD hm') hmt
    have hc₂ : C.q₂ + ((0 : E d), P.μ) = C.phat := by
      rw [← ContactData.ctr₂, C.ctr₂_eq_pstar_add, h2, pstar_add_south]
    have hzero := C.exterior_ball m hmD (by rw [hc₂]; exact stBallOpen_subset_stBall _ _ hm)
    exact hpos.ne' hzero
  · intro h1
    by_contra h2
    obtain ⟨m, hm, hm'⟩ := exists_mem_stBallOpen_inter_stBall C.ν₂_unit h2 P.μ_pos C.phat
    obtain ⟨hmD, hmt⟩ := mem_D₁_of_mem_dualBallOpen C hm
    have hc₂ : C.phat + ((0 : E d), P.μ) + P.μ • C.ν₂ = C.q₂ + ((0 : E d), P.μ) := by
      rw [← pstar_eq_phat_add, ← C.ctr₂_eq_pstar_add, ContactData.ctr₂]
    rw [hc₂] at hm'
    have hc₁ : C.q₁ + ((0 : E d), P.μ) = C.phat := by
      rw [← ContactData.ctr₁, C.ctr₁_eq_pstar_add, h1, pstar_add_south]
    have hE := C.interior_ball m hmD (by rw [hc₁]; exact stBallOpen_subset_stBall _ _ hm)
    exact C.exterior_past m hE hm' hmt

end Polar

end BernoulliComparison
