/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.Bridge

/-!
# Relaxed subsolutions are subcaloric; supersolutions are supercaloric where positive

* `IsParaRelaxedSub.subcaloric`: if `(u, E)` is a relaxed subsolution in `U × I`, then `u` is a
  viscosity subsolution of the heat equation in `U × I` (crossing in `U × I`, not only in `E`).
* `IsParaSuper.supercaloric_on_pos`: a supersolution `v` is a viscosity supersolution of the heat
  equation in `{v > 0} ∩ (U × I)`.

The definitions `IsCaloricSub`, `IsCaloricSuper` are in `Touching/Crossing.lean`. The time set `I`
is assumed to contain a left neighbourhood of each of its points (`I ∈ 𝓝[≤] t` for `t ∈ I`), as
`I = Ioc 0 T` does (`Ioc_mem_nhdsLE_of_mem`); no hypothesis on `Q` is needed.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-- `Ioc a b` contains a left neighbourhood of each of its points. -/
theorem Ioc_mem_nhdsLE_of_mem {a b t : ℝ} (ht : t ∈ Ioc a b) : Ioc a b ∈ 𝓝[≤] t :=
  mem_of_superset (Ioc_mem_nhdsLE ht.1) (Ioc_subset_Ioc_right ht.2)

theorem parCyl_subset_closedParCyl {x : E d} {t r : ℝ} : parCyl x t r ⊆ closedParCyl x t r :=
  fun _ hq ↦ ⟨ball_subset_closedBall hq.1, Ioc_subset_Icc_self hq.2⟩

/-- For `p.1 ∈ U` (open) and `I ∈ 𝓝[≤] p.2`, there are arbitrarily small `ρ > 0` with
`closedParCyl p ρ ⊆ U × I`. -/
theorem exists_closedParCyl_subset_prod {U : Set (E d)} {I : Set ℝ} {p : E d × ℝ}
    (hU : IsOpen U) (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ r₀ ∧ closedParCyl p.1 p.2 ρ ⊆ U ×ˢ I := by
  obtain ⟨ρ, ⟨hρ0, hρ⟩, hsub⟩ :=
    (Filter.Eventually.and (Ioo_mem_nhdsGT hr₀ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 r₀)
      (eventually_closedParCyl_subset_prod hU hpU hpI)).exists
  exact ⟨ρ, hρ0, hρ.le, hsub⟩

section Sub

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)}

/-- Subcaloricity. The function part of a relaxed subsolution is a viscosity subsolution
of the heat equation in `U × I` (crossing in `U × I`).

If `u(p) > 0`, then `p ∈ {u > 0} ⊆ E` and the crossing restricts to `E`; the relaxed bridge
applies and its free-boundary alternative is excluded by `φ(p) = u(p) > 0`. If `u(p) = 0`, then
`φ ≥ u ≥ 0 = φ(p)` on the backward cylinder, so `x ↦ φ(x, t₀)` has a local minimum at `x₀`
(`Δφ(p) ≥ 0`) and `s ↦ φ(x₀, s)` a minimum at `t₀` among earlier times (`∂ₜφ(p) ≤ 0`). -/
theorem IsParaRelaxedSub.subcaloric (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) : IsCaloricSub (U ×ˢ I) u := by
  intro φ hφ p hcross
  have hpUI : p ∈ U ×ˢ I := hcross.mem
  have hpI : I ∈ 𝓝[≤] p.2 := hI p.2 hpUI.2
  obtain ⟨r₀, hr₀, hle⟩ := hcross.2.2
  obtain ⟨ρ, hρ, hρr₀, hρsub⟩ := exists_closedParCyl_subset_prod hU hpUI.1 hpI hr₀
  have hcylUI : parCyl p.1 p.2 ρ ⊆ U ×ˢ I := parCyl_subset_closedParCyl.trans hρsub
  have hu0 : 0 ≤ u p := hsub.2.1 p hpUI
  rcases hu0.lt_or_eq with hpos | hzero
  · -- positive contact value: cross in `E` and apply the bridge
    have hpS : p ∈ S := hsub.2.2.2.2.1 ⟨hpUI, hpos⟩
    have hcrossS : CrossesFromAbove S u φ p :=
      hcross.of_local hpS hρ fun q hq ↦ hcylUI hq.2
    exact hsub.heat_nonpos_of_pos hU hpUI.1 hpI hφ hcrossS hpos
  · -- zero contact value: second-order conditions at a minimum
    have hφp : φ p = 0 := by rw [← hcross.eq, hzero]
    have hge : ∀ q ∈ parCyl p.1 p.2 ρ, φ p ≤ φ q := fun q hq ↦ by
      rw [hφp]
      exact (hsub.2.1 q (hcylUI hq)).trans (hle q ⟨hcylUI hq, parCyl_mono hρ.le hρr₀ hq⟩)
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
    have hmin : IsLocalMin (fun y ↦ φ (y, p.2)) p.1 := by
      filter_upwards [ball_mem_nhds p.1 hρ] with y hy
      exact hge (y, p.2) (mem_parCyl.2 ⟨hy, by nlinarith, le_rfl⟩)
    have hminT : IsLocalMinOn (fun s ↦ φ (p.1, s)) (Iic p.2) p.2 := by
      have : Ioc (p.2 - ρ ^ 2) p.2 ∈ 𝓝[≤] p.2 := Ioc_mem_nhdsLE (by nlinarith)
      filter_upwards [this] with s hs
      exact hge (p.1, s) (mem_parCyl.2 ⟨by simpa using hρ, hs.1, hs.2⟩)
    have h1 := lapₓ_nonneg_of_isLocalMin hφ2 hmin
    have h2 := dₜ_nonpos_of_isLocalMinOn_Iic (hφ2.differentiable two_ne_zero) hminT
    linarith

end Sub

section Super

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {v : E d × ℝ → ℝ}

/-- Supercaloricity. A supersolution is a viscosity supersolution of the heat equation in
its positivity set `{v > 0} ∩ (U × I)`: a crossing there is a crossing in `U × I` (the positivity
set is relatively open), and the free-boundary alternative of the bridge is excluded by
`φ(p) = v(p) > 0`. -/
theorem IsParaSuper.supercaloric_on_pos (hsup : IsParaSuper U Q I v) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) : IsCaloricSuper (posSetP v (U ×ˢ I)) v := by
  intro φ hφ p hcross
  obtain ⟨hpUI, hpos⟩ := hcross.mem
  -- `{v > 0}` is relatively open in `U × I`
  have hev : ∀ᶠ q in 𝓝 p, q ∈ U ×ˢ I → 0 < v q :=
    eventually_nhdsWithin_iff.1 ((hsup.1 p hpUI).eventually (lt_mem_nhds hpos))
  obtain ⟨ρ, hρ, hρsub⟩ :=
    (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0)
      (eventually_forall_closedParCyl hev)).exists
  have hcrossUI : CrossesFromBelow (U ×ˢ I) v φ p :=
    hcross.of_local hpUI hρ fun q hq ↦ ⟨hq.1, hρsub q (parCyl_subset_closedParCyl hq.2) hq.1⟩
  exact hsup.heat_nonneg_of_pos hU (hI p.2 hpUI.2) hφ hcrossUI hpos

end Super

end BernoulliComparison
