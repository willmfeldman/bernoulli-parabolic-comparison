/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.ParOpen
public import BernoulliComparison.Touching.Extend

/-!
# Touching classes with local test functions

Touching is a derived notion: these classes are never used to define solutions (solutions are
defined by barriers, `Interface/Parabolic.lean`); `Touching/ClassBridge.lean` proves that the
barrier classes belong to them.

Test functions are *local* (`IsTestFunAt φ p`: `C^∞` on an open set containing `p`), `Q` is a
function, and touching is `CrossesFromAbove`/`CrossesFromBelow` (`Touching/Crossing.lean`). The
parameter `O` is meant to be parabolically open (`IsParOpen`, `Touching/ParOpen.lean`); this is
not part of the definitions, and is assumed only in the lemmas that need it.

## Main definitions

* `TouchSub O Eset u Q` (written `TSub(O,E,u,Q)` in docstrings), `TouchSuper O v Q`
  (`TSuper(O,v,Q)`);
* `IsSubcal O w` (`Subcal(O,w)`), `IsSupercal O w` (`Supercal(O,w)`): viscosity
  sub/supersolutions of the heat equation with local test functions. `IsCaloricSub`,
  `IsCaloricSuper` use global test functions; the two notions are equivalent
  (`isCaloricSub_iff_isSubcal`, `isCaloricSuper_iff_isSupercal` in `Touching/ClassBridge.lean`).

## Main statements

* `touchSub_iff_contDiff`, `touchSuper_iff_contDiff`, `isSubcal_iff_contDiff`,
  `isSupercal_iff_contDiff`: the classes may be tested with globally `C^∞` functions only
  (by the bump extension of `Touching/Extend.lean` and locality (d) below);
* basic properties: (a) `TouchSub.restrict`, `TouchSuper.restrict`, `IsSubcal.restrict`,
  `IsSupercal.restrict`; (b) `TouchSub.mono_Q`, `TouchSuper.mono_Q`; (c) `TouchSub.smul`,
  `TouchSuper.smul`, `IsSubcal.smul`, `IsSupercal.smul` (and `iff` forms); (d) locality is in
  `Touching/Extend.lean` (`crossesFromAbove_congr_of_eventuallyEq`) and `Heat/Local.lean`
  (`CrossesFromAbove.congr_of_eventuallyEq`, `dₜ_congr_of_eventuallyEq`, …).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Definitions -/

/-- The class `TSub(O,E,u,Q)`: for every `p ∈ E ∩ O` and every test function
`φ` at `p` touching `u` from above in `E` at `p`: `(∂ₜφ - Δφ)(p) ≤ 0`, or `φ(p) = 0` and
`|∇φ(p)| ≥ Q(x₀)`. -/
def TouchSub (O Eset : Set (E d × ℝ)) (u : E d × ℝ → ℝ) (Q : E d → ℝ) : Prop :=
  ∀ p ∈ Eset ∩ O, ∀ φ : E d × ℝ → ℝ, IsTestFunAt φ p → CrossesFromAbove Eset u φ p →
    dₜ φ p - lapₓ φ p ≤ 0 ∨ (φ p = 0 ∧ Q p.1 ≤ ‖gradₓ φ p‖)

/-- The class `TSuper(O,v,Q)`: for every `p ∈ O` and every test function `φ` at
`p` touching `v` from below in `O` at `p`: `(∂ₜφ - Δφ)(p) ≥ 0`, or `φ(p) = 0` and
`|∇φ(p)| ≤ Q(x₀)`. -/
def TouchSuper (O : Set (E d × ℝ)) (v : E d × ℝ → ℝ) (Q : E d → ℝ) : Prop :=
  ∀ p ∈ O, ∀ φ : E d × ℝ → ℝ, IsTestFunAt φ p → CrossesFromBelow O v φ p →
    0 ≤ dₜ φ p - lapₓ φ p ∨ (φ p = 0 ∧ ‖gradₓ φ p‖ ≤ Q p.1)

/-- The class `Subcal(O,w)`: for every `p ∈ O` and every test function `φ` at
`p` touching `w` from above in `O` at `p`: `(∂ₜφ - Δφ)(p) ≤ 0`. (Local-test version of
`IsCaloricSub`, see `isCaloricSub_iff_isSubcal`.) -/
def IsSubcal (O : Set (E d × ℝ)) (w : E d × ℝ → ℝ) : Prop :=
  ∀ p ∈ O, ∀ φ : E d × ℝ → ℝ, IsTestFunAt φ p → CrossesFromAbove O w φ p →
    dₜ φ p - lapₓ φ p ≤ 0

/-- The class `Supercal(O,w)`: for every `p ∈ O` and every test function `φ` at
`p` touching `w` from below in `O` at `p`: `(∂ₜφ - Δφ)(p) ≥ 0`. (Local-test version of
`IsCaloricSuper`, see `isCaloricSuper_iff_isSupercal`.) -/
def IsSupercal (O : Set (E d × ℝ)) (w : E d × ℝ → ℝ) : Prop :=
  ∀ p ∈ O, ∀ φ : E d × ℝ → ℝ, IsTestFunAt φ p → CrossesFromBelow O w φ p →
    0 ≤ dₜ φ p - lapₓ φ p

/-! ### Testing with globally smooth functions -/

section Global

variable {O O' Eset : Set (E d × ℝ)} {u v w : E d × ℝ → ℝ} {Q Q' : E d → ℝ}

/-- The classes can be tested with globally `C^∞` functions (by the bump extension of
`Touching/Extend.lean` and locality of touching). -/
theorem touchSub_iff_contDiff :
    TouchSub O Eset u Q ↔ ∀ p ∈ Eset ∩ O, ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ →
      CrossesFromAbove Eset u φ p → dₜ φ p - lapₓ φ p ≤ 0 ∨ (φ p = 0 ∧ Q p.1 ≤ ‖gradₓ φ p‖) :=
  forall₂_congr fun _ _ ↦ forall_isTestFunAt_crossesFromAbove_iff fun _ _ h ↦ by
    rw [dₜ_congr_of_eventuallyEq h, lapₓ_congr_of_eventuallyEq h,
      gradₓ_congr_of_eventuallyEq h, h.eq_of_nhds]; exact id

theorem touchSuper_iff_contDiff :
    TouchSuper O v Q ↔ ∀ p ∈ O, ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ →
      CrossesFromBelow O v φ p → 0 ≤ dₜ φ p - lapₓ φ p ∨ (φ p = 0 ∧ ‖gradₓ φ p‖ ≤ Q p.1) :=
  forall₂_congr fun _ _ ↦ forall_isTestFunAt_crossesFromBelow_iff fun _ _ h ↦ by
    rw [dₜ_congr_of_eventuallyEq h, lapₓ_congr_of_eventuallyEq h,
      gradₓ_congr_of_eventuallyEq h, h.eq_of_nhds]; exact id

theorem isSubcal_iff_contDiff :
    IsSubcal O w ↔ ∀ p ∈ O, ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ →
      CrossesFromAbove O w φ p → dₜ φ p - lapₓ φ p ≤ 0 :=
  forall₂_congr fun _ _ ↦ forall_isTestFunAt_crossesFromAbove_iff fun _ _ h ↦ by
    rw [dₜ_congr_of_eventuallyEq h, lapₓ_congr_of_eventuallyEq h]; exact id

theorem isSupercal_iff_contDiff :
    IsSupercal O w ↔ ∀ p ∈ O, ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ →
      CrossesFromBelow O w φ p → 0 ≤ dₜ φ p - lapₓ φ p :=
  forall₂_congr fun _ _ ↦ forall_isTestFunAt_crossesFromBelow_iff fun _ _ h ↦ by
    rw [dₜ_congr_of_eventuallyEq h, lapₓ_congr_of_eventuallyEq h]; exact id

end Global

/-! ### Restriction -/

section Restrict

variable {O O' Eset : Set (E d × ℝ)} {u v w : E d × ℝ → ℝ} {Q : E d → ℝ}

/-- Restriction for `TSub`: the touching condition does not mention `O`. -/
theorem TouchSub.restrict (h : TouchSub O Eset u Q) (hO'O : O' ⊆ O) : TouchSub O' Eset u Q :=
  fun p hp ↦ h p ⟨hp.1, hO'O hp.2⟩

/-- Restriction for `TSuper`: a touching in a parabolically open `O' ⊆ O` is a
touching in `O`. -/
theorem TouchSuper.restrict (h : TouchSuper O v Q) (hO'O : O' ⊆ O) (hO' : IsParOpen O') :
    TouchSuper O' v Q := fun p hp φ hφ hc ↦ by
  obtain ⟨ρ, hρ, hsub⟩ := hO'.exists_inter_parCyl_subset hp O
  exact h p (hO'O hp) φ hφ (hc.of_local (hO'O hp) hρ hsub)

/-- Restriction for `Subcal`. -/
theorem IsSubcal.restrict (h : IsSubcal O w) (hO'O : O' ⊆ O) (hO' : IsParOpen O') :
    IsSubcal O' w := fun p hp φ hφ hc ↦ by
  obtain ⟨ρ, hρ, hsub⟩ := hO'.exists_inter_parCyl_subset hp O
  exact h p (hO'O hp) φ hφ (hc.of_local (hO'O hp) hρ hsub)

/-- Restriction for `Supercal`. -/
theorem IsSupercal.restrict (h : IsSupercal O w) (hO'O : O' ⊆ O) (hO' : IsParOpen O') :
    IsSupercal O' w := fun p hp φ hφ hc ↦ by
  obtain ⟨ρ, hρ, hsub⟩ := hO'.exists_inter_parCyl_subset hp O
  exact h p (hO'O hp) φ hφ (hc.of_local (hO'O hp) hρ hsub)

end Restrict

/-! ### Monotonicity in `Q` -/

section MonoQ

variable {O Eset : Set (E d × ℝ)} {u v : E d × ℝ → ℝ} {Q Q' : E d → ℝ}

/-- Monotonicity in `Q` for `TSub`: if `Q ≤ Q'` over `O`, then `TSub(O,E,u,Q')` implies
`TSub(O,E,u,Q)`. -/
theorem TouchSub.mono_Q (h : TouchSub O Eset u Q') (hQ : ∀ p ∈ O, Q p.1 ≤ Q' p.1) :
    TouchSub O Eset u Q := fun p hp φ hφ hc ↦
  (h p hp φ hφ hc).imp_right fun h' ↦ ⟨h'.1, (hQ p hp.2).trans h'.2⟩

/-- Monotonicity in `Q` for `TSuper`: if `Q ≤ Q'` over `O`, then `TSuper(O,v,Q)` implies
`TSuper(O,v,Q')`. -/
theorem TouchSuper.mono_Q (h : TouchSuper O v Q) (hQ : ∀ p ∈ O, Q p.1 ≤ Q' p.1) :
    TouchSuper O v Q' := fun p hp φ hφ hc ↦
  (h p hp φ hφ hc).imp_right fun h' ↦ ⟨h'.1, h'.2.trans (hQ p hp)⟩

end MonoQ

/-! ### Scaling -/

section Scaling

variable {S : Set (E d × ℝ)} {u φ : E d × ℝ → ℝ} {p : E d × ℝ} {c : ℝ}

theorem CrossesFromAbove.smul (h : CrossesFromAbove S u φ p) (hc : 0 ≤ c) :
    CrossesFromAbove S (c • u) (c • φ) p := by
  obtain ⟨hp, heq, r, hr, hle⟩ := h
  exact ⟨hp, by simp [heq], r, hr, fun q hq ↦ by
    simpa using mul_le_mul_of_nonneg_left (hle q hq) hc⟩

theorem CrossesFromBelow.smul (h : CrossesFromBelow S u φ p) (hc : 0 ≤ c) :
    CrossesFromBelow S (c • u) (c • φ) p := by
  obtain ⟨hp, heq, r, hr, hle⟩ := h
  exact ⟨hp, by simp [heq], r, hr, fun q hq ↦ by
    simpa using mul_le_mul_of_nonneg_left (hle q hq) hc⟩

theorem dₜ_smul (φ : E d × ℝ → ℝ) (c : ℝ) (q : E d × ℝ) : dₜ (c • φ) q = c * dₜ φ q := by
  simp only [dₜ, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem gradₓ_smul (hφ : ContDiff ℝ 1 φ) (c : ℝ) (q : E d × ℝ) :
    gradₓ (c • φ) q = c • gradₓ φ q := by
  have := gradₓ_const_mul (hφ.differentiable one_ne_zero) c q
  simpa [Pi.smul_def] using this

theorem lapₓ_smul (hφ : ContDiff ℝ 2 φ) (c : ℝ) (q : E d × ℝ) :
    lapₓ (c • φ) q = c * lapₓ φ q := by
  have := lapₓ_const_mul hφ c q
  simpa [Pi.smul_def] using this

end Scaling

section ScalingClasses

variable {O Eset : Set (E d × ℝ)} {u v w : E d × ℝ → ℝ} {Q : E d → ℝ} {c : ℝ}

/-- Scaling for `TSub`: for `c > 0`, `TSub(O,E,u,Q)` implies
`TSub(O,E,c u,c Q)`. -/
theorem TouchSub.smul (h : TouchSub O Eset u Q) (hc : 0 < c) : TouchSub O Eset (c • u) (c • Q) := by
  rw [touchSub_iff_contDiff] at h ⊢
  intro p hp φ hφ hcross
  have hψ : ContDiff ℝ ∞ (c⁻¹ • φ) := contDiff_const.smul hφ
  have hcr : CrossesFromAbove Eset u (c⁻¹ • φ) p := by
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hcross.smul (inv_nonneg.2 hc.le)
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have h1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  rcases h p hp _ hψ hcr with hH | ⟨h0, hgr⟩
  · left
    rw [dₜ_smul, lapₓ_smul h2, ← mul_sub] at hH
    exact nonpos_of_mul_nonpos_right hH (inv_pos.2 hc)
  · right
    rw [gradₓ_smul h1, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)] at hgr
    simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero, hc.ne', false_or] at h0
    refine ⟨h0, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rwa [le_inv_mul_iff₀ hc] at hgr

/-- Scaling for `TSuper`: for `c > 0`, `TSuper(O,v,Q)` implies
`TSuper(O,c v,c Q)`. -/
theorem TouchSuper.smul (h : TouchSuper O v Q) (hc : 0 < c) : TouchSuper O (c • v) (c • Q) := by
  rw [touchSuper_iff_contDiff] at h ⊢
  intro p hp φ hφ hcross
  have hψ : ContDiff ℝ ∞ (c⁻¹ • φ) := contDiff_const.smul hφ
  have hcr : CrossesFromBelow O v (c⁻¹ • φ) p := by
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hcross.smul (inv_nonneg.2 hc.le)
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have h1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  rcases h p hp _ hψ hcr with hH | ⟨h0, hgr⟩
  · left
    rw [dₜ_smul, lapₓ_smul h2, ← mul_sub] at hH
    exact nonneg_of_mul_nonneg_right hH (inv_pos.2 hc)
  · right
    rw [gradₓ_smul h1, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)] at hgr
    simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero, hc.ne', false_or] at h0
    refine ⟨h0, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rwa [inv_mul_le_iff₀ hc] at hgr

/-- Scaling for `Subcal`: invariance under multiplication by `c > 0`. -/
theorem IsSubcal.smul (h : IsSubcal O w) (hc : 0 < c) : IsSubcal O (c • w) := by
  rw [isSubcal_iff_contDiff] at h ⊢
  intro p hp φ hφ hcross
  have hψ : ContDiff ℝ ∞ (c⁻¹ • φ) := contDiff_const.smul hφ
  have hcr : CrossesFromAbove O w (c⁻¹ • φ) p := by
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hcross.smul (inv_nonneg.2 hc.le)
  have hH := h p hp _ hψ hcr
  rw [dₜ_smul, lapₓ_smul (hφ.of_le (by norm_cast)), ← mul_sub] at hH
  exact nonpos_of_mul_nonpos_right hH (inv_pos.2 hc)

/-- Scaling for `Supercal`: invariance under multiplication by `c > 0`. -/
theorem IsSupercal.smul (h : IsSupercal O w) (hc : 0 < c) : IsSupercal O (c • w) := by
  rw [isSupercal_iff_contDiff] at h ⊢
  intro p hp φ hφ hcross
  have hψ : ContDiff ℝ ∞ (c⁻¹ • φ) := contDiff_const.smul hφ
  have hcr : CrossesFromBelow O w (c⁻¹ • φ) p := by
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hcross.smul (inv_nonneg.2 hc.le)
  have hH := h p hp _ hψ hcr
  rw [dₜ_smul, lapₓ_smul (hφ.of_le (by norm_cast)), ← mul_sub] at hH
  exact nonneg_of_mul_nonneg_right hH (inv_pos.2 hc)

theorem touchSub_smul_iff (hc : 0 < c) : TouchSub O Eset (c • u) (c • Q) ↔ TouchSub O Eset u Q :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using h.smul (inv_pos.2 hc),
    fun h ↦ h.smul hc⟩

theorem touchSuper_smul_iff (hc : 0 < c) : TouchSuper O (c • v) (c • Q) ↔ TouchSuper O v Q :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using h.smul (inv_pos.2 hc),
    fun h ↦ h.smul hc⟩

theorem isSubcal_smul_iff (hc : 0 < c) : IsSubcal O (c • w) ↔ IsSubcal O w :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using h.smul (inv_pos.2 hc),
    fun h ↦ h.smul hc⟩

theorem isSupercal_smul_iff (hc : 0 < c) : IsSupercal O (c • w) ↔ IsSupercal O w :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using h.smul (inv_pos.2 hc),
    fun h ↦ h.smul hc⟩

end ScalingClasses

end BernoulliComparison
