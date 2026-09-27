/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.Caloric

/-!
# Parabolically open sets

A set `O ⊆ ℝ^{d+1}` is *parabolically open* if every `p ∈ O` has a closed backward cylinder
`C_r(p) = B̄_r(x) × [t - r², t] ⊆ O` (`r > 0`).

## Main statements

* `IsOpen.isParOpen`, `IsParOpen.inter`, `isParOpen_prod` (`U × I` with `U` open and `I`
  containing a left neighbourhood of each of its points), `isParOpen_prod_Ioc`;
* `IsParOpen.sep`, `IsParOpen.posSetP`: `{p ∈ O : w p > 0}` is parabolically open for `w`
  continuous on `O`;
* `IsParOpen.exists_parCyl_subset`, `IsParOpen.exists_inter_parCyl_subset`: the forms used to move
  touching between sets.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

variable {d : ℕ}

theorem closedParCyl_mono {x : E d} {t r r' : ℝ} (hr : 0 ≤ r) (hrr' : r ≤ r') :
    closedParCyl x t r ⊆ closedParCyl x t r' := by
  intro q hq
  rw [mem_closedParCyl] at hq ⊢
  refine ⟨hq.1.trans hrr', ?_, hq.2.2⟩
  nlinarith [hq.2.1]

/-- `S` is parabolically open if every `p ∈ S` has a closed backward
cylinder `closedParCyl p.1 p.2 r ⊆ S` with `r > 0`. -/
def IsParOpen (S : Set (E d × ℝ)) : Prop :=
  ∀ p ∈ S, ∃ r > 0, closedParCyl p.1 p.2 r ⊆ S

section

variable {S T : Set (E d × ℝ)} {p : E d × ℝ}

/-- In a parabolically open set, all small closed backward cylinders at `p ∈ S` lie in `S`. -/
theorem IsParOpen.eventually_closedParCyl_subset (hS : IsParOpen S) (hp : p ∈ S) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), closedParCyl p.1 p.2 r ⊆ S := by
  obtain ⟨r₀, hr₀, hsub⟩ := hS p hp
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r ⟨hr, hrr₀⟩
  exact (closedParCyl_mono hr.le hrr₀.le).trans hsub

/-- In a parabolically open set, every `p ∈ S` has an open backward cylinder `parCyl ⊆ S`. -/
theorem IsParOpen.exists_parCyl_subset (hS : IsParOpen S) (hp : p ∈ S) :
    ∃ ρ > 0, parCyl p.1 p.2 ρ ⊆ S := by
  obtain ⟨r, hr, hsub⟩ := hS p hp
  exact ⟨r, hr, parCyl_subset_closedParCyl.trans hsub⟩

/-- The form of parabolic openness used by `CrossesFromAbove.of_local` and
`IsCaloricSub.mono`: near `p ∈ S` (backward in time), any `T` is contained in `S`. -/
theorem IsParOpen.exists_inter_parCyl_subset (hS : IsParOpen S) (hp : p ∈ S) (T : Set (E d × ℝ)) :
    ∃ ρ > 0, T ∩ parCyl p.1 p.2 ρ ⊆ S := by
  obtain ⟨ρ, hρ, hsub⟩ := hS.exists_parCyl_subset hp
  exact ⟨ρ, hρ, fun q hq ↦ hsub hq.2⟩

/-- Open sets are parabolically open. -/
theorem _root_.IsOpen.isParOpen (hS : IsOpen S) : IsParOpen S := fun _ hp ↦
  (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0)
    (eventually_forall_closedParCyl (P := (· ∈ S)) (hS.mem_nhds hp))).exists

theorem isParOpen_univ : IsParOpen (univ : Set (E d × ℝ)) := isOpen_univ.isParOpen

theorem isParOpen_empty : IsParOpen (∅ : Set (E d × ℝ)) := isOpen_empty.isParOpen

/-- Finite intersections of parabolically open sets are parabolically open. -/
theorem IsParOpen.inter (hS : IsParOpen S) (hT : IsParOpen T) : IsParOpen (S ∩ T) :=
  fun _ hp ↦ ((hS.eventually_closedParCyl_subset hp.1).and
    ((hT.eventually_closedParCyl_subset hp.2).and
      (self_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0))).exists.imp
    fun _ h ↦ ⟨h.2.2, subset_inter h.1 h.2.1⟩

/-- `U × I` is parabolically open if `U` is open and `I` contains a left neighbourhood of each of
its points (e.g. `I = Ioc a b`). -/
theorem isParOpen_prod {U : Set (E d)} {I : Set ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) :
    IsParOpen (U ×ˢ I) := fun _ hp ↦
  ((eventually_closedParCyl_subset_prod hU hp.1 (hI _ hp.2)).and
    (self_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0)).exists.imp fun _ h ↦ ⟨h.2, h.1⟩

/-- `W × (α, β]` is parabolically open for `W` open. -/
theorem isParOpen_prod_Ioc {U : Set (E d)} (hU : IsOpen U) (a b : ℝ) :
    IsParOpen (U ×ˢ Ioc a b) :=
  isParOpen_prod hU fun _ ht ↦ Ioc_mem_nhdsLE_of_mem ht

/-- A subset `{p ∈ S | P p}` of a parabolically open `S` is parabolically open if `P` holds on `S`
near each of its points. -/
theorem IsParOpen.sep (hS : IsParOpen S) {P : E d × ℝ → Prop}
    (hP : ∀ p ∈ S, P p → ∀ᶠ q in 𝓝 p, q ∈ S → P q) : IsParOpen {p ∈ S | P p} := fun p hp ↦
  ((hS.eventually_closedParCyl_subset hp.1).and
    ((eventually_forall_closedParCyl (hP p hp.1 hp.2)).and
      (self_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0))).exists.imp
    fun _ h ↦ ⟨h.2.2, fun q hq ↦ ⟨h.1 hq, h.2.1 q hq (h.1 hq)⟩⟩

/-- If `w` is continuous on a parabolically open `S`, then `{p ∈ S | 0 < w p}` is parabolically
open. -/
theorem IsParOpen.posSetP (hS : IsParOpen S) {w : E d × ℝ → ℝ} (hw : ContinuousOn w S) :
    IsParOpen (posSetP w S) :=
  hS.sep fun p hp hpos ↦
    eventually_nhdsWithin_iff.1 ((hw p hp).eventually (lt_mem_nhds hpos))

end

end BernoulliComparison
