/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.Geometry
public import BernoulliComparison.Contact.TouchConfig

/-!
# First contact points

Under the crossing hypothesis
`S = {p ∈ E₁ | u₁ p ≥ v₁ p} ≠ ∅`, `Config.first_crossing` gives the first crossing time `t⋆`
and the contact set `Ξ`. `Config.IsFirstContact P p` records that `p = (x⋆, t⋆) ∈ Ξ` together with
the conclusions of `Config.first_crossing` at `t⋆ = p.2`; it is the output of
`Config.exists_isFirstContact` (from `Config.first_crossing`), not an assumption about the data.

Consequences used throughout the contact analysis: `x⋆ ∈ U₁`, `2μ < t⋆ ≤ T`, `ρ₀ ≤ t⋆`, the room
`B̄_{2r₀}(x⋆) × [t⋆ - 2r₀, t⋆] ⊆ U₁ × (2μ, T]` with `2λ < r₀`, and past points of `E₁` at every
point of `E₁ ∩ (U₁ × (2μ, T])` (`Config.past_points_of_mem`).
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Crossing

namespace Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} (P : Config U Q T u v Eset)

/-- `p = (x⋆, t⋆)` is a point of the contact set `Ξ` at the first crossing time `t⋆ = p.2`:
`p ∈ E₁ ∩ R₁`, `u₁ p = v₁ p`, `u₁ < v₁` on `E₁ ∩ {t < t⋆}` and `u₁ ≤ v₁` on `E₁ ∩ {t = t⋆}`.
Produced by `exists_isFirstContact`. -/
structure IsFirstContact (p : E d × ℝ) : Prop where
  mem_E₁ : p ∈ P.E₁
  u₁_eq_v₁ : P.u₁ p = P.v₁ p
  mem_R₁ : p ∈ P.R₁
  lt_of_lt : ∀ q ∈ P.E₁, q.2 < p.2 → P.u₁ q < P.v₁ q
  le_of_eq : ∀ q ∈ P.E₁, q.2 = p.2 → P.u₁ q ≤ P.v₁ q

/-- Under the crossing hypothesis there is a first contact point. -/
theorem exists_isFirstContact (hne : P.crossingSet.Nonempty) : ∃ p, P.IsFirstContact p := by
  obtain ⟨tstar, -, -, -, -, hlt, hle, ⟨p, hpE, hpt, hpeq⟩, -, hΞS, hSR⟩ := P.first_crossing hne
  refine ⟨p, hpE, hpeq, hSR (hΞS ⟨hpE, hpt, hpeq⟩), fun q hq hqt ↦ hlt q hq (hpt ▸ hqt),
    fun q hq hqt ↦ hle q hq (hpt ▸ hqt)⟩

/-- `U₁ × (2μ, T] ⊆ D₁`. -/
theorem prod_Ioc_subset_D₁ : P.U₁ ×ˢ Ioc (2 * P.μ) T ⊆ P.D₁ :=
  prod_mono subset_closure Ioc_subset_Icc_self

/-- `U₀ × (0, T] ⊆ D₀`. -/
theorem prod_Ioc_subset_D₀ : P.U₀ ×ˢ Ioc 0 T ⊆ P.D₀ :=
  prod_mono subset_closure Ioc_subset_Icc_self

/-- `Q₁⁻` is continuous at points of `U₁`. -/
theorem continuousAt_Qsub₁ {x : E d} (hx : x ∈ P.U₁) : ContinuousAt P.Qsub₁ x :=
  P.continuousOn_Qsub₁.continuousAt (P.isOpen_U₁.mem_nhds hx)

/-- Past points for `(u₁, E₁)` at any point of `E₁ ∩ (U₁ × (2μ, T])`, Euclidean
form: for every `ε > 0` there is `q ∈ E₁` with `q.2 < p.2` and `|q - p| < ε`. -/
theorem past_points_of_mem {p : E d × ℝ} (hpE : p ∈ P.E₁) (hp : p ∈ P.U₁ ×ˢ Ioc (2 * P.μ) T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ P.E₁, q.2 < p.2 ∧ ‖q.1 - p.1‖ ^ 2 + (q.2 - p.2) ^ 2 < ε ^ 2 :=
  P.isParaRelaxedSub_one.past_points_euclidean P.isOpen_U₁ hp.1 (Ioc_mem_nhdsLE_of_mem hp.2)
    (P.continuousAt_Qsub₁ hp.1) (P.Qsub₁_pos (subset_closure (P.U₁_subset hp.1))) hpE hε

namespace IsFirstContact

variable {P} {p : E d × ℝ} (h : P.IsFirstContact p)
include h

theorem mem_D₁ : p ∈ P.D₁ := P.E₁_subset_D₁ h.mem_E₁

theorem mem_U₁_Ioc : p ∈ P.U₁ ×ˢ Ioc (2 * P.μ) T := P.mem_U₁_Ioc_of_mem_R₁ h.mem_R₁

theorem fst_mem_U₁ : p.1 ∈ P.U₁ := h.mem_U₁_Ioc.1

theorem fst_mem_U : p.1 ∈ U := P.U₁_subset h.fst_mem_U₁

theorem fst_mem_closure : p.1 ∈ closure U := subset_closure h.fst_mem_U

theorem two_μ_lt : 2 * P.μ < p.2 := h.mem_U₁_Ioc.2.1

theorem le_T : p.2 ≤ T := h.mem_U₁_Ioc.2.2

theorem ρ₀_le : P.ρ₀ ≤ p.2 := h.mem_R₁.2.1

/-- The room at the contact point, from the margin of the convolved pair. -/
theorem room : closedBall p.1 (2 * P.r₀) ×ˢ Icc (p.2 - 2 * P.r₀) p.2 ⊆
    P.U₁ ×ˢ Ioc (2 * P.μ) T ∧ 2 * P.lam < P.r₀ :=
  P.room h.mem_R₁

theorem two_lam_lt_r₀ : 2 * P.lam < P.r₀ := h.room.2

/-- A convenient form of the room: points with `‖x - x⋆‖ ≤ 2r₀` and `t⋆ - 2r₀ ≤ t ≤ t⋆` lie in
`U₁ × (2μ, T]`. -/
theorem mem_room {q : E d × ℝ} (hx : ‖q.1 - p.1‖ ≤ 2 * P.r₀) (ht1 : p.2 - 2 * P.r₀ ≤ q.2)
    (ht2 : q.2 ≤ p.2) : q ∈ P.U₁ ×ˢ Ioc (2 * P.μ) T :=
  h.room.1 ⟨by rwa [mem_closedBall, dist_eq_norm], ht1, ht2⟩

/-- `0 ≤ u₁ p⋆`. -/
theorem u₁_nonneg : 0 ≤ P.u₁ p := P.u₁_nonneg h.mem_D₁

end IsFirstContact

end Config

end Crossing

end BernoulliComparison
