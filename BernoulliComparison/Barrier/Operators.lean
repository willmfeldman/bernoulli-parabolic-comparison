/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Setting
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Barrier toolkit: operator lemmas (scaling and translation)

Behaviour of `dₜ`, `lapₓ`, `gradₓ` under positive scaling of a
smooth test function `φ`, and under space-time translation. These are the calculus facts feeding
`Barrier/Classical.lean` (transformation of `IsClassicalStrictParaSub/Super`) and
`Barrier/Structural.lean` (`.smul`, `.translate` for the solution classes).

Since `φ : E d × ℝ → ℝ` is `ContDiff ℝ ∞`, every differentiability side condition is automatic;
we state the lemmas with the (weaker) `ContDiffAt`/`DifferentiableAt` hypothesis actually needed,
so each lemma is usable in isolation and callers derive it from `ContDiff.contDiffAt`.

**Elaboration note.** Every lambda binder below is annotated `fun y : E d ↦ …` (never left to be
inferred). Without the annotation, `Δ (fun y ↦ …)` sometimes fails to elaborate (`Laplacian`'s
`outParam` resolution gets stuck) once `Mathlib.Analysis.Calculus.Gradient.Basic` is in scope,
even though the same term elaborates fine in isolation; the explicit annotation sidesteps it.
-/

@[expose] public section

open scoped Gradient Laplacian ContDiff
open InnerProductSpace

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Smoothness of time- and space-slices of a globally smooth `φ` -/

/-- The time-slice `s ↦ φ (x, s)` of a globally smooth `φ` is smooth. -/
theorem ContDiff.sliceTime {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E d) :
    ContDiff ℝ ∞ (fun s ↦ φ (x, s)) :=
  hφ.comp (contDiff_const.prodMk contDiff_id)

/-- The space-slice `y ↦ φ (y, t)` of a globally smooth `φ` is smooth. -/
theorem ContDiff.sliceSpace {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : E d ↦ φ (y, t)) :=
  hφ.comp (contDiff_id.prodMk contDiff_const)

/-- A globally smooth `φ` has a well-defined `dₜ` everywhere. -/
theorem ContDiff.differentiableAt_dₜ {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : E d × ℝ) :
    DifferentiableAt ℝ (fun s ↦ φ (p.1, s)) p.2 :=
  (ContDiff.sliceTime hφ p.1).differentiable (by simp) _

/-- A globally smooth `φ` has a well-defined `gradₓ` everywhere. -/
theorem ContDiff.differentiableAt_gradₓ {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : E d × ℝ) :
    DifferentiableAt ℝ (fun y : E d ↦ φ (y, p.2)) p.1 :=
  (ContDiff.sliceSpace hφ p.2).differentiable (by simp) _

/-- A globally smooth `φ` has a well-defined `lapₓ` everywhere. -/
theorem ContDiff.contDiffAt_lapₓ {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : E d × ℝ) :
    ContDiffAt ℝ 2 (fun y : E d ↦ φ (y, p.2)) p.1 := by
  have h2 : ContDiff ℝ 2 (fun y : E d ↦ φ (y, p.2)) :=
    ContDiff.of_le (ContDiff.sliceSpace hφ p.2) (WithTop.coe_le_coe.mpr le_top)
  exact ContDiff.contDiffAt h2

/-! ### Scaling by a positive constant -/

section Smul

variable (c : ℝ) (φ : E d × ℝ → ℝ) (p : E d × ℝ)

/-- `(c • φ)` applied at a point unfolds to `c * φ p`; recorded for `simp`. -/
theorem smul_apply_eq (p : E d × ℝ) : (c • φ) p = c * φ p := rfl

/-- Time derivative of `c • φ`, given `φ` differentiable in time at `p`. -/
theorem dₜ_const_smul (h : DifferentiableAt ℝ (fun s ↦ φ (p.1, s)) p.2) :
    dₜ (c • φ) p = c * dₜ φ p := by
  simp only [dₜ, smul_apply_eq]
  exact deriv_const_mul c h

/-- Spatial Laplacian of `c • φ`, given `φ` twice continuously differentiable in space at `p`. -/
theorem lapₓ_const_smul (h : ContDiffAt ℝ 2 (fun y : E d ↦ φ (y, p.2)) p.1) :
    lapₓ (c • φ) p = c * lapₓ φ p := by
  have heq : (fun y : E d ↦ (c • φ) (y, p.2)) = c • (fun y : E d ↦ φ (y, p.2)) := by
    funext y; exact smul_apply_eq c φ (y, p.2)
  change Δ (fun y : E d ↦ (c • φ) (y, p.2)) p.1 = c * Δ (fun y : E d ↦ φ (y, p.2)) p.1
  rw [heq]
  exact laplacian_smul c h

/-- Spatial gradient of `c • φ`, given `φ` differentiable in space at `p`. -/
theorem gradₓ_const_smul (h : DifferentiableAt ℝ (fun y : E d ↦ φ (y, p.2)) p.1) :
    gradₓ (c • φ) p = c • gradₓ φ p := by
  have heq : (fun y : E d ↦ (c • φ) (y, p.2)) = c • (fun y : E d ↦ φ (y, p.2)) := by
    funext y; exact smul_apply_eq c φ (y, p.2)
  change ∇ (fun y : E d ↦ (c • φ) (y, p.2)) p.1 = c • ∇ (fun y : E d ↦ φ (y, p.2)) p.1
  rw [heq]
  unfold gradient
  rw [fderiv_const_smul h c]
  simp

/-- Norm of the spatial gradient of `c • φ`. -/
theorem norm_gradₓ_const_smul (h : DifferentiableAt ℝ (fun y : E d ↦ φ (y, p.2)) p.1) :
    ‖gradₓ (c • φ) p‖ = |c| * ‖gradₓ φ p‖ := by
  rw [gradₓ_const_smul c φ p h, norm_smul, Real.norm_eq_abs]

/-- `{c • φ > 0} = {φ > 0}` for `c > 0`. -/
theorem posSet_const_smul_of_pos {c : ℝ} (hc : 0 < c) :
    {q : E d × ℝ | 0 < (c • φ) q} = {q | 0 < φ q} := by
  ext q
  simp only [smul_apply_eq, Set.mem_setOf_eq]
  rw [mul_pos_iff_of_pos_left hc]

end Smul

/-! ### Translation by a fixed shift `k : E d × ℝ` -/

section Translate

variable (k : E d × ℝ) (φ : E d × ℝ → ℝ) (p : E d × ℝ)

/-- Time derivative commutes with translation. -/
theorem dₜ_comp_sub : dₜ (fun q ↦ φ (q - k)) p = dₜ φ (p - k) := by
  have hp1 : (p - k).1 = p.1 - k.1 := rfl
  have hp2 : (p - k).2 = p.2 - k.2 := rfl
  have key :
      deriv (fun s ↦ φ (p.1 - k.1, s - k.2)) p.2 = deriv (fun s ↦ φ (p.1 - k.1, s)) (p.2 - k.2) :=
    deriv_comp_sub_const (f := fun s ↦ φ (p.1 - k.1, s)) k.2 p.2
  change deriv (fun s ↦ φ ((p.1, s) - k)) p.2 = deriv (fun s ↦ φ ((p - k).1, s)) (p - k).2
  rw [hp1, hp2]
  have e1 : (fun s ↦ φ ((p.1, s) - k)) = fun s ↦ φ (p.1 - k.1, s - k.2) := by
    funext s; congr 1
  rw [e1]
  exact key

/-- Spatial gradient commutes with translation. -/
theorem gradₓ_comp_sub : gradₓ (fun q ↦ φ (q - k)) p = gradₓ φ (p - k) := by
  have hp1 : (p - k).1 = p.1 - k.1 := rfl
  have hp2 : (p - k).2 = p.2 - k.2 := rfl
  have key : ∇ (fun y : E d ↦ φ ((y, p.2) - k)) p.1 =
      ∇ (fun y : E d ↦ φ (y, p.2 - k.2)) (p.1 - k.1) := by
    have e1 : (fun y : E d ↦ φ ((y, p.2) - k)) =
        fun y ↦ (fun z : E d ↦ φ (z, p.2 - k.2)) (y - k.1) := by
      funext y; congr 1
    rw [e1]
    unfold gradient
    exact congrArg _ (fderiv_comp_sub (f := fun z : E d ↦ φ (z, p.2 - k.2)) k.1)
  change ∇ (fun y : E d ↦ φ ((y, p.2) - k)) p.1 = ∇ (fun y : E d ↦ φ (y, (p - k).2)) (p - k).1
  rw [hp1, hp2]
  exact key

/-- The Laplacian commutes with translation, on any finite-dimensional real inner product space:
both sides are traces of the second derivative, and `iteratedFDeriv_comp_sub` moves the shift. -/
theorem laplacian_comp_sub_const {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : F → ℝ) (a x : F) :
    Δ (fun z : F ↦ f (z - a)) x = Δ f (x - a) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_sub]

/-- Spatial Laplacian commutes with translation. The proof goes through the general
`laplacian_comp_sub_const`, stated on an abstract inner product space `F`, which avoids an
elaboration problem with the direct statement on `E d`. -/
theorem lapₓ_comp_sub : lapₓ (fun q ↦ φ (q - k)) p = lapₓ φ (p - k) := by
  have e1 : (fun y : E d ↦ φ ((y, p.2) - k)) =
      fun y : E d ↦ (fun z : E d ↦ φ (z, p.2 - k.2)) (y - k.1) := by
    funext y; rfl
  have h := laplacian_comp_sub_const (F := E d) (fun z : E d ↦ φ (z, p.2 - k.2)) k.1 p.1
  unfold lapₓ
  rw [e1]
  exact h

/-- `{φ ∘ (· - k) > 0} = (· + k) '' {φ > 0}`, equivalently `(fun q ↦ q + k) '' {φ > 0}`. -/
theorem posSet_comp_sub_eq :
    {q : E d × ℝ | 0 < φ (q - k)} = (fun q ↦ q + k) '' {q | 0 < φ q} := by
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h; exact ⟨q - k, h, sub_add_cancel q k⟩
  · rintro ⟨q', hq', rfl⟩
    rwa [add_sub_cancel_right]

end Translate

end BernoulliComparison
