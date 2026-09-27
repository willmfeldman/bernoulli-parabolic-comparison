/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Parabolic

/-!
# Barrier toolkit: the closed domain `Ū × [α, β]`

`U × (α, β]` is dense in `Ū × [α, β]`, and nonnegativity /
positivity-set inclusions transfer from the half-open domain to the closed one by density and
continuity. Used in `Convolution/` and `Crossing/Config.lean`.
-/

@[expose] public section

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-- `closure (U ×ˢ (α, β]) = Ū × [α, β]` for `α < β`. -/
theorem closure_prod_Ioc_eq {U : Set (E d)} {α β : ℝ} (h : α < β) :
    closure (U ×ˢ Ioc α β) = closure U ×ˢ Icc α β := by
  rw [closure_prod_eq, closure_Ioc h.ne]

/-- `U × (α, β]` is contained in the closed domain `closure U ×ˢ Icc α β`. -/
theorem prod_Ioc_subset_closure {U : Set (E d)} {α β : ℝ} :
    U ×ˢ Ioc α β ⊆ closure U ×ˢ Icc α β :=
  prod_mono subset_closure Ioc_subset_Icc_self

/-- A function continuous on `Ū × [α, β]` and nonnegative on
`U × (α, β]` is nonnegative on all of `Ū × [α, β]`. -/
theorem nonneg_on_closedDomain {U : Set (E d)} {α β : ℝ} {w : E d × ℝ → ℝ} (hα : α < β)
    (hw : ContinuousOn w (closure U ×ˢ Icc α β)) (hnonneg : ∀ p ∈ U ×ˢ Ioc α β, 0 ≤ w p) :
    ∀ p ∈ closure U ×ˢ Icc α β, 0 ≤ w p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p, hpD, hneg⟩ := hcon
  have hev : ∀ᶠ q in 𝓝[closure U ×ˢ Icc α β] p, w q < 0 :=
    (hw p hpD).eventually_lt continuousWithinAt_const hneg
  obtain ⟨O, hOo, hpO, hOsub⟩ := mem_nhdsWithin.1 hev
  rw [← closure_prod_Ioc_eq hα] at hpD
  obtain ⟨q, hqO, hq⟩ := mem_closure_iff_nhds.1 hpD O (hOo.mem_nhds hpO)
  exact absurd (hnonneg q hq) (not_le.mpr (hOsub ⟨hqO, prod_Ioc_subset_closure hq⟩))

/-- If `E` is closed and contains `{p ∈ U ×ˢ (α, β] | 0 < w p}`,
it contains `{p ∈ Ū × [α, β] | 0 < w p}`. -/
theorem posSet_closedDomain_subset {U : Set (E d)} {α β : ℝ} {w : E d × ℝ → ℝ}
    {Eset : Set (E d × ℝ)} (hα : α < β) (hw : ContinuousOn w (closure U ×ˢ Icc α β))
    (hE : IsClosed Eset) (hsub : {p ∈ U ×ˢ Ioc α β | 0 < w p} ⊆ Eset) :
    {p ∈ closure U ×ˢ Icc α β | 0 < w p} ⊆ Eset := by
  have hmem : ∀ p ∈ closure U ×ˢ Icc α β, 0 < w p →
      p ∈ closure {q ∈ U ×ˢ Ioc α β | 0 < w q} := by
    intro p hpD hpos
    have hev : ∀ᶠ q in 𝓝[closure U ×ˢ Icc α β] p, 0 < w q :=
      continuousWithinAt_const.eventually_lt (hw p hpD) hpos
    obtain ⟨O, hOo, hpO, hOsub⟩ := mem_nhdsWithin.1 hev
    rw [mem_closure_iff_nhds]
    intro t ht
    rw [← closure_prod_Ioc_eq hα] at hpD
    obtain ⟨q, ⟨hqt, hqO⟩, hq⟩ :=
      mem_closure_iff_nhds.1 hpD (t ∩ O) (inter_mem ht (hOo.mem_nhds hpO))
    exact ⟨q, hqt, hq, hOsub ⟨hqO, prod_Ioc_subset_closure hq⟩⟩
  rintro p ⟨hpD, hpos⟩
  have := closure_mono hsub (hmem p hpD hpos)
  rwa [hE.closure_eq] at this

end BernoulliComparison
