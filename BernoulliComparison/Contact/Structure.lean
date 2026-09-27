/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.ZeroContact

/-!
# The contact structure

At a first contact point `p⋆ = (x⋆, t⋆)`:

(i) `E₁ ∩ {t < t⋆} ⊆ {v₁ > 0}` (`contact_structure_pos`);
(ii) `p⋆ ∈ closure (E₁ ∩ {t < t⋆})` (`contact_structure_past`);
(iii) `v₁(p⋆) = 0` and `p⋆ ∈ closure {p ∈ D₁ | v₁ p > 0, p.2 < t⋆}` (`contact_structure_pos_past`);
(iv) (exterior past points) `p⋆ ∈ closure ((D₁ \ E₁) ∩ {t < t⋆})`
(`contact_structure_exterior_past`).

`contact_structure` bundles (i)–(iv). Closures are topological; the neighbourhoods in the proof of
(iv) are taken in the sup metric of `E d × ℝ` (equivalent to the Euclidean one for closures).
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Contact

open Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset} {p : E d × ℝ}

/-- Contact structure (i): `E₁ ∩ {t < t⋆} ⊆ {v₁ > 0}`. -/
theorem contact_structure_pos (h : P.IsFirstContact p) :
    ∀ q ∈ P.E₁, q.2 < p.2 → 0 < P.v₁ q := fun q hq hqt ↦
  (P.u₁_nonneg (P.E₁_subset_D₁ hq)).trans_lt (h.lt_of_lt q hq hqt)

/-- Contact structure (ii): `p⋆ ∈ closure (E₁ ∩ {t < t⋆})`. -/
theorem contact_structure_past (h : P.IsFirstContact p) :
    p ∈ closure (P.E₁ ∩ {q | q.2 < p.2}) :=
  P.past_points ⟨h.mem_E₁, h.mem_R₁⟩

/-- Contact structure (iii): `v₁(p⋆) = 0` and `p⋆` is a limit of points of `D₁` in
the strict past where `v₁ > 0`. -/
theorem contact_structure_pos_past (h : P.IsFirstContact p) :
    P.v₁ p = 0 ∧ p ∈ closure {q ∈ P.D₁ | 0 < P.v₁ q ∧ q.2 < p.2} :=
  ⟨(zero_contact h).2, closure_mono (fun q (hq : q ∈ P.E₁ ∩ {q | q.2 < p.2}) ↦
    (⟨P.E₁_subset_D₁ hq.1, contact_structure_pos h q hq.1 hq.2, hq.2⟩ :
      q ∈ {q ∈ P.D₁ | 0 < P.v₁ q ∧ q.2 < p.2}))
    (contact_structure_past h)⟩

/-- Contact structure (iv), exterior past points:
`p⋆ ∈ closure ((D₁ \ E₁) ∩ {t < t⋆})`. -/
theorem contact_structure_exterior_past (h : P.IsFirstContact p) :
    p ∈ closure ((P.D₁ \ P.E₁) ∩ {q | q.2 < p.2}) := by
  by_contra hcon
  rw [Metric.mem_closure_iff] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfar⟩ := hcon
  have hr₀ := P.r₀_pos
  set ρ := min (min ε P.r₀) 1 / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have : min (min ε P.r₀) 1 ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hρr : ρ ≤ P.r₀ := by
    have : min (min ε P.r₀) 1 ≤ P.r₀ := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hρ1 : ρ ≤ 1 / 2 := by
    have : min (min ε P.r₀) 1 ≤ 1 := min_le_right _ _
    linarith
  set τ := ρ ^ 2 / (4 * ((d : ℝ) + 1)) with hτdef
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hτ : 0 < τ := by positivity
  have hτρ : τ ≤ ρ := by
    rw [hτdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hτd : 4 * d * (p.2 - (p.2 - τ)) ≤ ρ ^ 2 := by
    rw [sub_sub_cancel, hτdef, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ρ]
  have hsub : closedBall p.1 ρ ×ˢ Icc (p.2 - τ) p.2 ⊆ P.U₁ ×ˢ Ioc (2 * P.μ) T := by
    rintro q ⟨hq1, hq2⟩
    rw [mem_closedBall, dist_eq_norm] at hq1
    exact h.mem_room (by linarith) (by linarith [hq2.1]) hq2.2
  have hpos : ∀ q ∈ closedBall p.1 ρ ×ˢ Ico (p.2 - τ) p.2, 0 < P.v₁ q := by
    rintro q ⟨hq1, hq2⟩
    have hqD : q ∈ P.D₁ := P.prod_Ioc_subset_D₁ (hsub ⟨hq1, Ico_subset_Icc_self hq2⟩)
    have hdist : dist p q < ε := by
      rw [mem_closedBall, dist_comm] at hq1
      have h2 : dist p.2 q.2 < ε := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonpos (by linarith [hq2.2])]
        linarith [hq2.1]
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by linarith, h2⟩
    have hqE : q ∈ P.E₁ := by
      by_contra hqE
      exact absurd (hfar q ⟨⟨hqD, hqE⟩, hq2.2⟩) (not_le.2 hdist)
    exact contact_structure_pos h q hqE hq2.2
  have hv := bump_positivity_pos (P.continuousOn_v₁.mono P.prod_Ioc_subset_D₁)
    P.isSupercal_one hρ (by linarith) hτd hsub hpos
  rw [(zero_contact h).2] at hv
  exact lt_irrefl _ hv

/-- The contact structure, (i)–(iv) together. -/
theorem contact_structure (h : P.IsFirstContact p) :
    (∀ q ∈ P.E₁, q.2 < p.2 → 0 < P.v₁ q) ∧
    p ∈ closure (P.E₁ ∩ {q | q.2 < p.2}) ∧
    (P.v₁ p = 0 ∧ p ∈ closure {q ∈ P.D₁ | 0 < P.v₁ q ∧ q.2 < p.2}) ∧
    p ∈ closure ((P.D₁ \ P.E₁) ∩ {q | q.2 < p.2}) :=
  ⟨contact_structure_pos h, contact_structure_past h, contact_structure_pos_past h,
    contact_structure_exterior_past h⟩

end Contact

end BernoulliComparison
