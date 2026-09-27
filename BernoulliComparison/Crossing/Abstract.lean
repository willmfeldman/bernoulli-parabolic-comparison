/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Abstract first crossing

The abstract first-crossing lemma `first_crossing`. Given a compact
space-time domain `D₁`, a closed subset `E₁ ⊆ D₁`, continuous `f, g` on `D₁` with `f < g` on
`E₁ \ R₁` for some "room" set `R₁`, and hypothesis (TS) ("no instant creation": every point of
`E₁ ∩ R₁` is a limit from the strict past within `E₁`), the crossing set
`S := {p ∈ E₁ | f p ≥ g p}` (if nonempty) has a first time `t⋆`, before which `f < g` on `E₁`, at
which `f ≤ g` on `E₁`, and the contact set `Ξ := {p ∈ E₁ | p.2 = t⋆ ∧ f p = g p}` is nonempty,
compact, and contained in `S ⊆ R₁`.

This file is independent of the convolved configuration (`Crossing/Config.lean`); the ambient
space is a generic `Y × ℝ` (space `Y`, time `ℝ`). The instance for the configuration is
`Config.first_crossing` in `Crossing/Instance.lean`.

The first crossing time `t⋆` is the minimum *time* of the compact set `S` (via
`IsCompact.exists_isMinOn` on `Prod.snd`), not a supremum of "good" times. The "top slice"
subtlety (the contact time slice itself) is exactly hypothesis (TS), which is taken as an explicit
hypothesis; for the configuration it is supplied by `Config.past_points`, from
`IsParaRelaxedSub.past_points`.

The proof uses `le_on_closure` (Mathlib `Topology/Order/OrderClosed.lean`) in place of an explicit
sequential/net argument for the "top slice" step (ii): `f ≤ g` propagates from a set to its
closure once both functions are continuous there, which is exactly hypothesis (TS).
-/

@[expose] public section

open Set Filter Topology

namespace BernoulliComparison

namespace Crossing

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- Abstract first crossing. Let `D₁ ⊆ Y × ℝ` be compact, `E₁ ⊆ D₁`
closed, `f, g` continuous on `D₁`, and `R₁ ⊆ Y × ℝ` such that `f < g` on `E₁ \ R₁` and (TS) every
`p ∈ E₁ ∩ R₁` lies in the closure of `E₁ ∩ {q | q.2 < p.2}`. If `S := {p ∈ E₁ | g p ≤ f p}` is
nonempty, then it has a point `p₀` minimizing the time coordinate on `S`, and with `t⋆ := p₀.2`:
(i) `f < g` on `E₁ ∩ {t < t⋆}`; (ii) `f ≤ g` on `E₁ ∩ {t = t⋆}`; (iii) the contact set
`Ξ := {p ∈ E₁ | p.2 = t⋆ ∧ f p = g p}` is nonempty, compact, and `Ξ ⊆ S ⊆ R₁`. -/
theorem first_crossing
    {D₁ : Set (Y × ℝ)} (hD₁ : IsCompact D₁)
    {E₁ : Set (Y × ℝ)} (hE₁ : IsClosed E₁) (hE₁D₁ : E₁ ⊆ D₁)
    {f g : Y × ℝ → ℝ} (hf : ContinuousOn f D₁) (hg : ContinuousOn g D₁)
    {R₁ : Set (Y × ℝ)}
    (hgap : ∀ p ∈ E₁ \ R₁, f p < g p)
    (hTS : ∀ p ∈ E₁ ∩ R₁, p ∈ closure (E₁ ∩ {q : Y × ℝ | q.2 < p.2}))
    (hne : {p ∈ E₁ | g p ≤ f p}.Nonempty) :
    ∃ p₀ ∈ {p ∈ E₁ | g p ≤ f p}, IsMinOn Prod.snd {p ∈ E₁ | g p ≤ f p} p₀ ∧
      (∀ p ∈ E₁, p.2 < p₀.2 → f p < g p) ∧
      (∀ p ∈ E₁, p.2 = p₀.2 → f p ≤ g p) ∧
      {p ∈ E₁ | p.2 = p₀.2 ∧ f p = g p}.Nonempty ∧
      IsCompact {p ∈ E₁ | p.2 = p₀.2 ∧ f p = g p} ∧
      {p ∈ E₁ | p.2 = p₀.2 ∧ f p = g p} ⊆ {p ∈ E₁ | g p ≤ f p} ∧
      {p ∈ E₁ | g p ≤ f p} ⊆ R₁ := by
  set S : Set (Y × ℝ) := {p ∈ E₁ | g p ≤ f p} with hSdef
  -- `S ⊆ R₁`: `f < g` off `R₁`.
  have hSR₁ : S ⊆ R₁ := by
    intro p hp
    by_contra hpR
    exact absurd hp.2 (not_le.2 (hgap p ⟨hp.1, hpR⟩))
  -- `S = E₁ ∩ {p ∈ D₁ | g p ≤ f p}` is closed, and compact (a closed subset of the compact `D₁`).
  have hSeq : S = E₁ ∩ {p ∈ D₁ | g p ≤ f p} := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpE, hple⟩
      exact ⟨hpE, hE₁D₁ hpE, hple⟩
    · rintro p ⟨hpE, -, hple⟩
      exact ⟨hpE, hple⟩
  have hSclosed : IsClosed S := hSeq ▸ hE₁.inter (hD₁.isClosed.isClosed_le hg hf)
  have hSsubD : S ⊆ D₁ := fun p hp ↦ hE₁D₁ hp.1
  have hScompact : IsCompact S := hD₁.of_isClosed_subset hSclosed hSsubD
  -- Extreme value theorem: `S` attains the minimum of the time coordinate at some `p₀`.
  obtain ⟨p₀, hp₀S, hp₀min⟩ := hScompact.exists_isMinOn hne continuous_snd.continuousOn
  have hmin : ∀ x ∈ S, p₀.2 ≤ x.2 := isMinOn_iff.mp hp₀min
  -- (i) `f < g` on `E₁ ∩ {t < t⋆}`.
  have hi : ∀ p ∈ E₁, p.2 < p₀.2 → f p < g p := by
    intro p hpE hlt
    by_contra hcon
    have hpS : p ∈ S := ⟨hpE, not_lt.1 hcon⟩
    exact absurd (hmin p hpS) (not_le.2 hlt)
  -- (ii) `f ≤ g` on `E₁ ∩ {t = t⋆}`, via `le_on_closure` and hypothesis (TS).
  have hii : ∀ p ∈ E₁, p.2 = p₀.2 → f p ≤ g p := by
    intro p hpE hp2
    by_cases hpR : p ∈ R₁
    · have hle : ∀ q ∈ E₁ ∩ {q : Y × ℝ | q.2 < p.2}, f q ≤ g q := by
        rintro q ⟨hqE, hqlt⟩
        rw [hp2] at hqlt
        exact (hi q hqE hqlt).le
      have hsubD : E₁ ∩ {q : Y × ℝ | q.2 < p.2} ⊆ D₁ := fun q hq ↦ hE₁D₁ hq.1
      have hclosuresub : closure (E₁ ∩ {q : Y × ℝ | q.2 < p.2}) ⊆ D₁ :=
        closure_minimal hsubD hD₁.isClosed
      exact le_on_closure hle (hf.mono hclosuresub) (hg.mono hclosuresub) (hTS p ⟨hpE, hpR⟩)
    · exact (hgap p ⟨hpE, hpR⟩).le
  refine ⟨p₀, hp₀S, hp₀min, hi, hii, ?_, ?_, ?_, hSR₁⟩
  · -- (iii) the contact set is nonempty: `p₀` itself is a contact point.
    exact ⟨p₀, hp₀S.1, rfl, le_antisymm (hii p₀ hp₀S.1 rfl) hp₀S.2⟩
  · -- (iii) the contact set is compact: it equals `(S ∩ {t = t⋆}) ∩ {p ∈ D₁ | f p ≤ g p}`.
    have hEq : {p ∈ E₁ | p.2 = p₀.2 ∧ f p = g p} = S ∩ {p : Y × ℝ | p.2 = p₀.2} ∩
        {p ∈ D₁ | f p ≤ g p} := by
      apply Set.Subset.antisymm
      · rintro p ⟨hpE, hp2, hfg⟩
        exact ⟨⟨⟨hpE, hfg.ge⟩, hp2⟩, hE₁D₁ hpE, hfg.le⟩
      · rintro p ⟨⟨⟨hpE, hge⟩, hp2⟩, -, hle⟩
        exact ⟨hpE, hp2, le_antisymm hle hge⟩
    rw [hEq]
    exact (hScompact.inter_right (isClosed_singleton.preimage continuous_snd)).inter_right
      (hD₁.isClosed.isClosed_le hf hg)
  · -- (iii) `Ξ ⊆ S`.
    rintro p ⟨hpE, -, hfg⟩
    exact ⟨hpE, hfg.ge⟩

end Crossing

end BernoulliComparison
