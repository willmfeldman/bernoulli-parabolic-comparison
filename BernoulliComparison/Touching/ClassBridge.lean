/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.Classes

/-!
# Barrier classes belong to the touching classes

The touching bridges and the sub/supercaloricity of barrier solutions, stated with local test
functions and the classes of `Touching/Classes.lean`. The proofs reduce to the statements for
globally `C^∞` test functions (`IsParaRelaxedSub.touching_alt`, `IsParaSuper.touching_alt`,
`IsParaRelaxedSub.subcaloric`, `IsParaSuper.supercaloric_on_pos`, in `Touching/Bridge.lean` and
`Touching/Caloric.lean`) by extending local test functions with a bump (`Touching/Extend.lean`).

## Main statements

* `isCaloricSub_iff_isSubcal`, `isCaloricSuper_iff_isSupercal`: the global-test classes
  `IsCaloricSub`/`IsCaloricSuper` coincide with the local-test classes `IsSubcal`/`IsSupercal`,
  on every set `O` (no parabolic openness needed: crossing only sees a neighbourhood of `p`).
* `IsParaRelaxedSub.touching_alt_of_isTestFunAt`, `IsParaSuper.touching_alt_of_isTestFunAt`:
  the touching bridges (pointwise, local test functions, `Q` continuous at `x₀`).
* `IsParaRelaxedSub.touchSub`, `IsParaSuper.touchSuper`: the class forms (`Q` continuous on `U`).
* `IsParaRelaxedSub.isSubcal`, `IsParaSuper.isSupercal_on_pos`: sub- and supercaloricity with
  local test functions.

As in `Touching/Caloric.lean`, the time set `I` is assumed to contain a left neighbourhood of each
of its points (`hI : ∀ t ∈ I, I ∈ 𝓝[≤] t`), as `I = Ioc α β` does (`Ioc_mem_nhdsLE_of_mem`).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Global versus local caloric classes -/

section Caloric

variable {O : Set (E d × ℝ)} {w : E d × ℝ → ℝ}

/-- `IsCaloricSub` (global `C^∞` tests) coincides with `IsSubcal` (local tests). -/
theorem isCaloricSub_iff_isSubcal : IsCaloricSub O w ↔ IsSubcal O w := by
  rw [isSubcal_iff_contDiff]
  exact ⟨fun h p _ φ hφ hc ↦ h φ hφ p hc, fun h φ hφ p hc ↦ h p hc.mem φ hφ hc⟩

/-- `IsCaloricSuper` (global `C^∞` tests) coincides with `IsSupercal` (local tests). -/
theorem isCaloricSuper_iff_isSupercal : IsCaloricSuper O w ↔ IsSupercal O w := by
  rw [isSupercal_iff_contDiff]
  exact ⟨fun h p _ φ hφ hc ↦ h φ hφ p hc, fun h φ hφ p hc ↦ h p hc.mem φ hφ hc⟩

alias ⟨IsCaloricSub.isSubcal, IsSubcal.isCaloricSub⟩ := isCaloricSub_iff_isSubcal

alias ⟨IsCaloricSuper.isSupercal, IsSupercal.isCaloricSuper⟩ := isCaloricSuper_iff_isSupercal

end Caloric

/-! ### Relaxed subsolutions -/

section Sub

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)}
  {φ : E d × ℝ → ℝ} {p : E d × ℝ}

/-- Relaxed-subsolution bridge with local test functions. If `(u, E)` is a relaxed subsolution, `Q`
is continuous at `x₀`, and a test function `φ` at `p = (x₀, t₀) ∈ U × I` touches `u` from above in
`E` at `p`, then `(∂ₜφ - Δφ)(p) ≤ 0`, or `φ(p) = 0` and `|∇φ(p)| ≥ Q(x₀)`. -/
theorem IsParaRelaxedSub.touching_alt_of_isTestFunAt (hsub : IsParaRelaxedSub U Q I u S)
    (hU : IsOpen U) (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) (hQ : ContinuousAt Q p.1)
    (hφ : IsTestFunAt φ p) (hcross : CrossesFromAbove S u φ p) :
    dₜ φ p - lapₓ φ p ≤ 0 ∨ (φ p = 0 ∧ Q p.1 ≤ ‖gradₓ φ p‖) := by
  refine (forall_isTestFunAt_crossesFromAbove_iff
    (P := fun φ ↦ dₜ φ p - lapₓ φ p ≤ 0 ∨ (φ p = 0 ∧ Q p.1 ≤ ‖gradₓ φ p‖)) ?_).2
    (fun ψ hψ hc ↦ hsub.touching_alt hU hpU hpI hQ hψ hc) φ hφ hcross
  intro _ _ h
  rw [dₜ_congr_of_eventuallyEq h, lapₓ_congr_of_eventuallyEq h,
      gradₓ_congr_of_eventuallyEq h, h.eq_of_nhds]
  exact id

/-- Relaxed-subsolution bridge, class form: if `Q` is continuous on `U`, then
`TSub(U × I, E, u, Q)`. -/
theorem IsParaRelaxedSub.touchSub (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) (hQ : ContinuousOn Q U) : TouchSub (U ×ˢ I) S u Q :=
  fun p hp _ hφ hcross ↦ hsub.touching_alt_of_isTestFunAt hU hp.2.1 (hI p.2 hp.2.2)
    (hQ.continuousAt (hU.mem_nhds hp.2.1)) hφ hcross

/-- Subcaloricity with local test functions: `Subcal(U × I, u)`. -/
theorem IsParaRelaxedSub.isSubcal (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) : IsSubcal (U ×ˢ I) u :=
  (hsub.subcaloric hU hI).isSubcal

end Sub

/-! ### Supersolutions -/

section Super

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {v : E d × ℝ → ℝ}
  {φ : E d × ℝ → ℝ} {p : E d × ℝ}

/-- Supersolution bridge with local test functions. If `v` is a supersolution, `Q` is continuous at
`x₀`, and a test function `φ` at `p = (x₀, t₀)` touches `v` from below in `U × I` at `p`, then
`(∂ₜφ - Δφ)(p) ≥ 0`, or `φ(p) = 0` and `|∇φ(p)| ≤ Q(x₀)`. -/
theorem IsParaSuper.touching_alt_of_isTestFunAt (hsup : IsParaSuper U Q I v) (hU : IsOpen U)
    (hpI : I ∈ 𝓝[≤] p.2) (hQ : ContinuousAt Q p.1) (hφ : IsTestFunAt φ p)
    (hcross : CrossesFromBelow (U ×ˢ I) v φ p) :
    0 ≤ dₜ φ p - lapₓ φ p ∨ (φ p = 0 ∧ ‖gradₓ φ p‖ ≤ Q p.1) := by
  refine (forall_isTestFunAt_crossesFromBelow_iff
    (P := fun φ ↦ 0 ≤ dₜ φ p - lapₓ φ p ∨ (φ p = 0 ∧ ‖gradₓ φ p‖ ≤ Q p.1)) ?_).2
    (fun ψ hψ hc ↦ hsup.touching_alt hU hpI hQ hψ hc) φ hφ hcross
  intro _ _ h
  rw [dₜ_congr_of_eventuallyEq h, lapₓ_congr_of_eventuallyEq h,
      gradₓ_congr_of_eventuallyEq h, h.eq_of_nhds]
  exact id

/-- Supersolution bridge, class form: if `Q` is continuous on `U`, then
`TSuper(U × I, v, Q)`. -/
theorem IsParaSuper.touchSuper (hsup : IsParaSuper U Q I v) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) (hQ : ContinuousOn Q U) : TouchSuper (U ×ˢ I) v Q :=
  fun p hp _ hφ hcross ↦ hsup.touching_alt_of_isTestFunAt hU (hI p.2 hp.2)
    (hQ.continuousAt (hU.mem_nhds hp.1)) hφ hcross

/-- The positivity set `{v > 0} ∩ (U × I)` of a supersolution is parabolically open. -/
theorem IsParaSuper.isParOpen_posSetP (hsup : IsParaSuper U Q I v) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) : IsParOpen (posSetP v (U ×ˢ I)) :=
  (isParOpen_prod hU hI).posSetP hsup.1

/-- Supercaloricity with local test functions: `Supercal({v > 0} ∩ (U × I), v)`. -/
theorem IsParaSuper.isSupercal_on_pos (hsup : IsParaSuper U Q I v) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) : IsSupercal (posSetP v (U ×ˢ I)) v :=
  (hsup.supercaloric_on_pos hU hI).isSupercal

end Super

end BernoulliComparison
