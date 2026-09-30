/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barrier.Operators
public import BernoulliComparison.Interface.Parabolic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Analysis.Normed.Group.Pointwise

/-!
# Barrier toolkit: transformation of classical strict barriers

Monotonicity in `Q`, positive scaling and space-time translation of `φ` for
`IsClassicalStrictParaSub`/`IsClassicalStrictParaSuper`. These feed the corresponding lemmas for
the solution classes `IsParaRelaxedSub`, `IsParaSuper` in `Barrier/Structural.lean`.
-/

@[expose] public section

open Set Filter Topology Pointwise
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Monotonicity in `Q` -/

/-- Increasing `Q` keeps a classical strict supersolution: `‖∇φ‖ < Q` on the free boundary is
easier to satisfy for a larger `Q`. -/
theorem IsClassicalStrictParaSuper.mono_Q {Q Q' : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} (h : IsClassicalStrictParaSuper Q φ V a b) (hQ : ∀ x, Q x ≤ Q' x) :
    IsClassicalStrictParaSuper Q' φ V a b :=
  ⟨h.1, h.2.1, fun p hp ↦ (h.2.2 p hp).trans_le (hQ p.1)⟩

/-- Decreasing `Q` keeps a classical strict subsolution: `Q < ‖∇φ‖` on the free boundary is
easier to satisfy for a smaller `Q`. -/
theorem IsClassicalStrictParaSub.mono_Q {Q Q' : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} (h : IsClassicalStrictParaSub Q' φ V a b) (hQ : ∀ x, Q x ≤ Q' x) :
    IsClassicalStrictParaSub Q φ V a b :=
  ⟨h.1, h.2.1, fun p hp ↦ (hQ p.1).trans_lt (h.2.2 p hp)⟩

/-! ### Positive scaling -/

/-- `PrecOn` is invariant under scaling both sides by the same positive constant. -/
theorem PrecOn.smul_iff {X : Type*} {u v : X → ℝ} {Eset F : Set X} {c : ℝ} (hc : 0 < c) :
    PrecOn (c • u) (c • v) Eset F ↔ PrecOn u v Eset F := by
  unfold PrecOn
  refine forall_congr' fun p ↦ forall_congr' fun _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_lt_mul_iff_right₀ hc

/-- `posSetP` is invariant under scaling `u` by a positive constant. -/
theorem posSetP_const_smul_of_pos {u : E d × ℝ → ℝ} {Ω : Set (E d × ℝ)} {c : ℝ} (hc : 0 < c) :
    posSetP (c • u) Ω = posSetP u Ω := by
  unfold posSetP
  ext p
  simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
  exact and_congr_right' (mul_pos_iff_of_pos_left hc)

/-- `Prec` is invariant under scaling both functions by the same positive constant. -/
theorem Prec.smul_iff {u v : E d × ℝ → ℝ} {Ω F : Set (E d × ℝ)} {c : ℝ} (hc : 0 < c) :
    Prec (c • u) (c • v) Ω F ↔ Prec u v Ω F := by
  unfold Prec
  rw [posSetP_const_smul_of_pos hc, PrecOn.smul_iff hc]

/-- Scaling a classical strict supersolution's test function `φ ↦ c • φ` (`c > 0`) turns a
barrier for `Q` into a barrier for `c • Q`. -/
theorem IsClassicalStrictParaSuper.const_smul {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} {c : ℝ} (hc : 0 < c) (h : IsClassicalStrictParaSuper Q φ V a b) :
    IsClassicalStrictParaSuper (c • Q) (c • φ) V a b := by
  obtain ⟨hφ, hpde, hgrad⟩ := h
  have hposeq : {q : E d × ℝ | 0 < (c • φ) q} = {q | 0 < φ q} := posSet_const_smul_of_pos φ hc
  refine ⟨ContDiff.const_smul c hφ, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [hposeq] at hp
    rw [dₜ_const_smul c φ p (ContDiff.differentiableAt_dₜ hφ p),
      lapₓ_const_smul c φ p (ContDiff.contDiffAt_lapₓ hφ p)]
    have := hpde p hp
    nlinarith
  · rw [show frontier {q : E d × ℝ | 0 < (c • φ) q} = frontier {q | 0 < φ q} by rw [hposeq]] at hp
    rw [norm_gradₓ_const_smul c φ p (ContDiff.differentiableAt_gradₓ hφ p), abs_of_pos hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (mul_lt_mul_iff_right₀ hc).mpr (hgrad p hp)

/-- Scaling a classical strict subsolution's test function `φ ↦ c • φ` (`c > 0`) turns a
barrier for `Q` into a barrier for `c • Q`. -/
theorem IsClassicalStrictParaSub.const_smul {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} {c : ℝ} (hc : 0 < c) (h : IsClassicalStrictParaSub Q φ V a b) :
    IsClassicalStrictParaSub (c • Q) (c • φ) V a b := by
  obtain ⟨hφ, hpde, hgrad⟩ := h
  have hposeq : {q : E d × ℝ | 0 < (c • φ) q} = {q | 0 < φ q} := posSet_const_smul_of_pos φ hc
  refine ⟨ContDiff.const_smul c hφ, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [hposeq] at hp
    rw [dₜ_const_smul c φ p (ContDiff.differentiableAt_dₜ hφ p),
      lapₓ_const_smul c φ p (ContDiff.contDiffAt_lapₓ hφ p)]
    have := hpde p hp
    nlinarith
  · rw [show frontier {q : E d × ℝ | 0 < (c • φ) q} = frontier {q | 0 < φ q} by rw [hposeq]] at hp
    rw [norm_gradₓ_const_smul c φ p (ContDiff.differentiableAt_gradₓ hφ p), abs_of_pos hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (mul_lt_mul_iff_right₀ hc).mpr (hgrad p hp)

/-- Scaling a barrier for `Q` by `c⁻¹ > 0` gives a barrier for `c⁻¹ • Q`; used as the converse
direction to `IsClassicalStrictParaSuper.const_smul`. -/
theorem IsClassicalStrictParaSuper.smul_iff {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} {c : ℝ} (hc : 0 < c) :
    IsClassicalStrictParaSuper (c • Q) φ V a b ↔ IsClassicalStrictParaSuper Q (c⁻¹ • φ) V a b := by
  constructor
  · intro h
    have := h.const_smul (inv_pos.mpr hc)
    rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  · intro h
    have := h.const_smul hc
    rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at this

/-- Scaling a barrier for `Q` by `c⁻¹ > 0` gives a barrier for `c⁻¹ • Q`; used as the converse
direction to `IsClassicalStrictParaSub.const_smul`. -/
theorem IsClassicalStrictParaSub.smul_iff {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} {c : ℝ} (hc : 0 < c) :
    IsClassicalStrictParaSub (c • Q) φ V a b ↔ IsClassicalStrictParaSub Q (c⁻¹ • φ) V a b := by
  constructor
  · intro h
    have := h.const_smul (inv_pos.mpr hc)
    rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  · intro h
    have := h.const_smul hc
    rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at this

/-! ### Space-time translation -/

/-- `A ×ˢ B` translates componentwise. -/
theorem image_add_prod {A : Set (E d)} {B : Set ℝ} {k : E d × ℝ} :
    (fun p : E d × ℝ ↦ p + k) '' (A ×ˢ B) = ((· + k.1) '' A) ×ˢ ((· + k.2) '' B) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q.1, hq.1, rfl⟩, ⟨q.2, hq.2, rfl⟩⟩
  · rintro ⟨⟨x, hx, hx'⟩, ⟨t, ht, ht'⟩⟩
    exact ⟨(x, t), ⟨hx, ht⟩, Prod.ext hx' ht'⟩

/-- A closed real interval translates to a closed real interval. -/
theorem image_add_right_Icc {a b c : ℝ} : (· + c) '' Icc a b = Icc (a + c) (b + c) := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨x - c, ⟨by linarith, by linarith⟩, by ring⟩

/-- Translation commutes with closure (stated with the plain lambda, so it `rw`s against
literal translation terms without needing `Homeomorph.addRight`'s coercion to match
syntactically). -/
theorem image_add_closure {A : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (k : A) (S : Set A) :
    (fun q ↦ q + k) '' closure S = closure ((fun q ↦ q + k) '' S) :=
  (Homeomorph.addRight k).image_closure S

/-- Translation commutes with frontier (see `image_add_closure`). -/
theorem image_add_frontier {A : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (k : A) (S : Set A) :
    (fun q ↦ q + k) '' frontier S = frontier ((fun q ↦ q + k) '' S) :=
  (Homeomorph.addRight k).image_frontier S

/-- Translating an admissible cylinder by `k`, assuming the
translated box lands inside `U × I`. -/
theorem AdmissibleCyl.translate {U' : Set (E d)} {I' : Set ℝ} {V : Set (E d)} {a b : ℝ}
    (hVab : AdmissibleCyl U' I' V a b) (k : E d × ℝ) {U : Set (E d)} {I : Set ℝ}
    (hUI : (fun p : E d × ℝ ↦ p + k) '' (U' ×ˢ I') ⊆ U ×ˢ I) :
    AdmissibleCyl U I ((· + k.1) '' V) (a + k.2) (b + k.2) := by
  obtain ⟨hVo, hVb, hab, hsub⟩ := hVab
  refine ⟨(Homeomorph.addRight k.1).isOpenMap V hVo, ?_, by linarith, ?_⟩
  · have h1 : Bornology.IsBounded ({k.1} : Set (E d)) := Bornology.isBounded_singleton
    have h2 : Bornology.IsBounded (V + {k.1}) := hVb.add h1
    rwa [add_singleton] at h2
  · have hclV : closure ((· + k.1) '' V) = (· + k.1) '' closure V :=
      (image_add_closure k.1 V).symm
    rw [hclV, ← image_add_right_Icc, ← image_add_prod]
    exact (Set.image_mono hsub).trans hUI

/-- Translating a classical strict supersolution's test function by
`k` gives a barrier for any `Q'` dominating the translate of `Q` on `closure V`. -/
theorem IsClassicalStrictParaSuper.translate {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} (h : IsClassicalStrictParaSuper Q φ V a b) (k : E d × ℝ) {Q' : E d → ℝ}
    (hQ' : ∀ x ∈ closure V, Q x ≤ Q' (x + k.1)) :
    IsClassicalStrictParaSuper Q' (fun q ↦ φ (q - k)) ((· + k.1) '' V) (a + k.2) (b + k.2) := by
  obtain ⟨hφ, hpde, hgrad⟩ := h
  have hφ' : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ φ (q - k)) :=
    ContDiff.comp hφ (contDiff_id.sub contDiff_const)
  have hpos_eq : {q : E d × ℝ | 0 < φ (q - k)} = (fun q ↦ q + k) '' {q | 0 < φ q} :=
    posSet_comp_sub_eq k φ
  have hcl_eq : closure {q : E d × ℝ | 0 < φ (q - k)} =
      (fun q ↦ q + k) '' closure {q | 0 < φ q} := by
    rw [hpos_eq, image_add_closure]
  have hfr_eq : frontier {q : E d × ℝ | 0 < φ (q - k)} =
      (fun q ↦ q + k) '' frontier {q | 0 < φ q} := by
    rw [hpos_eq, image_add_frontier]
  have hdom_eq : closure ((· + k.1) '' V) ×ˢ Icc (a + k.2) (b + k.2)
      = (fun q : E d × ℝ ↦ q + k) '' (closure V ×ˢ Icc a b) := by
    rw [← image_add_closure k.1 V, ← image_add_right_Icc, image_add_prod]
  refine ⟨hφ', fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rw [hcl_eq, hdom_eq, ← Set.image_inter (fun x y h ↦ by simpa using h)] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hHop : dₜ (fun q ↦ φ (q - k)) (p + k) - lapₓ (fun q ↦ φ (q - k)) (p + k)
        = dₜ φ p - lapₓ φ p := by
      have e1 : (p + k) - k = p := by abel
      rw [dₜ_comp_sub, lapₓ_comp_sub, e1]
    rw [hHop]
    exact hpde p hp
  · rw [hfr_eq, hdom_eq, ← Set.image_inter (fun x y h ↦ by simpa using h)] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have e1 : (p + k) - k = p := by abel
    have hgeq : gradₓ (fun q ↦ φ (q - k)) (p + k) = gradₓ φ p := by
      rw [gradₓ_comp_sub, e1]
    rw [hgeq]
    have hpx : (p + k).1 = p.1 + k.1 := rfl
    rw [hpx]
    exact (hgrad p hp).trans_le (hQ' p.1 hp.2.1)

/-- Translating a classical strict subsolution's test function by
`k` gives a barrier for any `Q'` dominated by the translate of `Q` on `closure V`. -/
theorem IsClassicalStrictParaSub.translate {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} (h : IsClassicalStrictParaSub Q φ V a b) (k : E d × ℝ) {Q' : E d → ℝ}
    (hQ' : ∀ x ∈ closure V, Q' (x + k.1) ≤ Q x) :
    IsClassicalStrictParaSub Q' (fun q ↦ φ (q - k)) ((· + k.1) '' V) (a + k.2) (b + k.2) := by
  obtain ⟨hφ, hpde, hgrad⟩ := h
  have hφ' : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ φ (q - k)) :=
    ContDiff.comp hφ (contDiff_id.sub contDiff_const)
  have hpos_eq : {q : E d × ℝ | 0 < φ (q - k)} = (fun q ↦ q + k) '' {q | 0 < φ q} :=
    posSet_comp_sub_eq k φ
  have hcl_eq : closure {q : E d × ℝ | 0 < φ (q - k)} =
      (fun q ↦ q + k) '' closure {q | 0 < φ q} := by
    rw [hpos_eq, image_add_closure]
  have hfr_eq : frontier {q : E d × ℝ | 0 < φ (q - k)} =
      (fun q ↦ q + k) '' frontier {q | 0 < φ q} := by
    rw [hpos_eq, image_add_frontier]
  have hdom_eq : closure ((· + k.1) '' V) ×ˢ Icc (a + k.2) (b + k.2)
      = (fun q : E d × ℝ ↦ q + k) '' (closure V ×ˢ Icc a b) := by
    rw [← image_add_closure k.1 V, ← image_add_right_Icc, image_add_prod]
  refine ⟨hφ', fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rw [hcl_eq, hdom_eq, ← Set.image_inter (fun x y h ↦ by simpa using h)] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hHop : dₜ (fun q ↦ φ (q - k)) (p + k) - lapₓ (fun q ↦ φ (q - k)) (p + k)
        = dₜ φ p - lapₓ φ p := by
      have e1 : (p + k) - k = p := by abel
      rw [dₜ_comp_sub, lapₓ_comp_sub, e1]
    rw [hHop]
    exact hpde p hp
  · rw [hfr_eq, hdom_eq, ← Set.image_inter (fun x y h ↦ by simpa using h)] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have e1 : (p + k) - k = p := by abel
    have hgeq : gradₓ (fun q ↦ φ (q - k)) (p + k) = gradₓ φ p := by
      rw [gradₓ_comp_sub, e1]
    rw [hgeq]
    have hpx : (p + k).1 = p.1 + k.1 := rfl
    rw [hpx]
    exact (hQ' p.1 hp.2.1).trans_lt (hgrad p hp)

end BernoulliComparison
