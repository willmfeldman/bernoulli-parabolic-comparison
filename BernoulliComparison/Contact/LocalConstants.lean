/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Crossing.Instance

/-!
# Local constants; the gap

For `x⋆ ∈ Ū` put `c₁ = (1 + δ)(Q(x⋆) - 3Lλ)` (`Config.cSub`) and `c₂ = (1 - δ)(Q(x⋆) + 3Lλ)`
(`Config.cSuper`). Then `0 < c₂ < c₁` (`Config.cSuper_pos`, `Config.cSuper_lt_cSub`), and on
`Ū ∩ B̄_{2λ}(x⋆)` the lower free-boundary coefficients `(1 + δ)Q`, `Q₀⁻`, `Q₁⁻` are `≥ c₁` and the
upper ones `(1 - δ)Q`, `Q₀⁺`, `Q₁⁺` are `≤ c₂` (`Config.local_constants`).
-/

@[expose] public section

open Set Metric

namespace BernoulliComparison

namespace Crossing

namespace Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} (P : Config U Q T u v Eset)

/-- The lower local constant `c₁ = (1 + δ)(Q(x⋆) - 3Lλ)` at `x⋆`. -/
def cSub (xstar : E d) : ℝ := (1 + P.δ) * (Q xstar - 3 * P.L * P.lam)

/-- The upper local constant `c₂ = (1 - δ)(Q(x⋆) + 3Lλ)` at `x⋆`. -/
def cSuper (xstar : E d) : ℝ := (1 - P.δ) * (Q xstar + 3 * P.L * P.lam)

/-- `6 L λ ≤ (3/4) δ c` from (P2). -/
theorem six_L_lam_le : 6 * (P.L : ℝ) * P.lam ≤ 3 / 4 * (P.δ * P.c) := by
  have h := P.P2
  rw [lam]
  nlinarith

/-- `|Q x - Q x⋆| ≤ 2Lλ` on `Ū ∩ B̄_{2λ}(x⋆)`. -/
theorem abs_Q_sub_le {xstar x : E d} (hxs : xstar ∈ closure U) (hx : x ∈ closure U)
    (hxx : dist x xstar ≤ 2 * P.lam) : |Q x - Q xstar| ≤ 2 * P.L * P.lam := by
  have h := P.lipschitzOnWith.dist_le_mul x hx xstar hxs
  rw [Real.dist_eq] at h
  have hL : (0 : ℝ) ≤ P.L := P.L.2
  calc |Q x - Q xstar| ≤ P.L * dist x xstar := h
    _ ≤ P.L * (2 * P.lam) := mul_le_mul_of_nonneg_left hxx hL
    _ = 2 * P.L * P.lam := by ring

/-- The gap: `0 < c₂`. -/
theorem cSuper_pos {xstar : E d} (hxs : xstar ∈ closure U) : 0 < P.cSuper xstar := by
  have hc := P.c_le xstar hxs
  have hL : (0 : ℝ) ≤ P.L := P.L.2
  have := P.lam_pos
  have := P.c_pos
  have h3 : 0 ≤ 3 * (P.L : ℝ) * P.lam := by positivity
  have h1 : 0 < Q xstar + 3 * P.L * P.lam := by linarith
  exact mul_pos P.one_sub_δ_pos h1

/-- The gap: `c₂ < c₁`. -/
theorem cSuper_lt_cSub {xstar : E d} (hxs : xstar ∈ closure U) :
    P.cSuper xstar < P.cSub xstar := by
  have hc := P.c_le xstar hxs
  have h6 := P.six_L_lam_le
  have hδ := P.δ_pos
  have hc0 := P.c_pos
  have hδc : P.δ * P.c ≤ P.δ * Q xstar := mul_le_mul_of_nonneg_left hc hδ.le
  have hδc0 : 0 < P.δ * P.c := mul_pos hδ hc0
  unfold cSub cSuper
  nlinarith

/-- `0 < c₁`. -/
theorem cSub_pos {xstar : E d} (hxs : xstar ∈ closure U) : 0 < P.cSub xstar :=
  (P.cSuper_pos hxs).trans (P.cSuper_lt_cSub hxs)

/-- Local constants: for `x⋆ ∈ Ū`, `c₁ = (1 + δ)(Q(x⋆) - 3Lλ)` and
`c₂ = (1 - δ)(Q(x⋆) + 3Lλ)` satisfy `0 < c₂ < c₁`, and for every `x ∈ Ū ∩ B̄_{2λ}(x⋆)`:
`min {(1 + δ) Q x, Q₀⁻ x, Q₁⁻ x} ≥ c₁` and `max {(1 - δ) Q x, Q₀⁺ x, Q₁⁺ x} ≤ c₂`. -/
theorem local_constants {xstar : E d} (hxs : xstar ∈ closure U) :
    0 < P.cSuper xstar ∧ P.cSuper xstar < P.cSub xstar ∧
    ∀ x ∈ closure U, dist x xstar ≤ 2 * P.lam →
      (P.cSub xstar ≤ (1 + P.δ) * Q x ∧ P.cSub xstar ≤ P.Qsub₀ x ∧
        P.cSub xstar ≤ P.Qsub₁ x) ∧
      ((1 - P.δ) * Q x ≤ P.cSuper xstar ∧ P.Qsuper₀ x ≤ P.cSuper xstar ∧
        P.Qsuper₁ x ≤ P.cSuper xstar) := by
  refine ⟨P.cSuper_pos hxs, P.cSuper_lt_cSub hxs, fun x hx hxx ↦ ?_⟩
  have hQ := abs_le.mp (P.abs_Q_sub_le hxs hx hxx)
  have hL : (0 : ℝ) ≤ P.L := P.L.2
  have hℓ := P.ℓ_lt_lam
  have hℓ0 := P.ℓ_pos
  have hl0 := P.lam_pos
  have hLℓ : (P.L : ℝ) * P.ℓ ≤ P.L * P.lam := mul_le_mul_of_nonneg_left hℓ.le hL
  have hLl : 0 ≤ (P.L : ℝ) * P.lam := mul_nonneg hL hl0.le
  have h1 := P.one_add_δ_pos
  have h2 := P.one_sub_δ_pos
  unfold cSub cSuper Qsub₀ Qsub₁ Qsuper₀ Qsuper₁
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact mul_le_mul_of_nonneg_left (by linarith) h1.le
  · exact mul_le_mul_of_nonneg_left (by linarith) h1.le
  · exact mul_le_mul_of_nonneg_left (by linarith) h1.le
  · exact mul_le_mul_of_nonneg_left (by linarith) h2.le
  · exact mul_le_mul_of_nonneg_left (by linarith) h2.le
  · exact mul_le_mul_of_nonneg_left (by linarith) h2.le

end Config

end Crossing

end BernoulliComparison
