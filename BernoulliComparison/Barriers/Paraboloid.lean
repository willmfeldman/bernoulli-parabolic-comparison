/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barriers.Radial

/-!
# The caloric paraboloid

For `x₀ ∈ ℝᵈ`, `t₁, ρ, κ ∈ ℝ`,
`P(x, t) = κ - |x - x₀|² / ρ² - 2d (t - t₁) / ρ²`
is `C^∞` on space-time and caloric: `∂ₜP = ΔP = -2d/ρ²`, `∇P = -(2/ρ²)(x - x₀)`. For `t ≥ t₁`:
`P ≤ κ`, `P ≤ κ - 1` wherever `|x - x₀| ≥ ρ > 0` (not only on the sphere `|x - x₀| = ρ`), and
`P(x₀, t) = κ - 2d(t - t₁)/ρ²`.

The paraboloid is the explicit caloric lower barrier in the bump-positivity estimate
(`Contact/BumpPositivity.lean`); no heat kernel is needed.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian ContDiff

namespace BernoulliComparison

variable {d : ℕ}

namespace Barriers

/-- The caloric paraboloid
`P(x, t) = κ - |x - x₀|² / ρ² - 2d (t - t₁) / ρ²`. -/
noncomputable def paraboloid (x₀ : E d) (t₁ ρ κ : ℝ) : E d × ℝ → ℝ :=
  fun p ↦ κ - ‖p.1 - x₀‖ ^ 2 / ρ ^ 2 - 2 * d * (p.2 - t₁) / ρ ^ 2

variable (x₀ : E d) (t₁ ρ κ : ℝ)

theorem paraboloid_apply (p : E d × ℝ) :
    paraboloid x₀ t₁ ρ κ p = κ - ‖p.1 - x₀‖ ^ 2 / ρ ^ 2 - 2 * d * (p.2 - t₁) / ρ ^ 2 := rfl

theorem contDiff_paraboloid {n : WithTop ℕ∞} : ContDiff ℝ n (paraboloid x₀ t₁ ρ κ) := by
  unfold paraboloid
  refine (contDiff_const.sub ?_).sub ?_
  · exact ((contDiff_fst.sub contDiff_const).norm_sq ℝ).div_const _
  · exact (contDiff_const.mul (contDiff_snd.sub contDiff_const)).div_const _

/-- `∂ₜP = -2d/ρ²`. -/
theorem dₜ_paraboloid (p : E d × ℝ) : dₜ (paraboloid x₀ t₁ ρ κ) p = -(2 * d / ρ ^ 2) := by
  have H : HasDerivAt (fun s ↦ κ - ‖p.1 - x₀‖ ^ 2 / ρ ^ 2 - 2 * d * (s - t₁) / ρ ^ 2)
      (-(2 * d * 1 / ρ ^ 2)) p.2 :=
    ((((hasDerivAt_id' p.2).sub_const t₁).const_mul (2 * (d : ℝ))).div_const (ρ ^ 2)).const_sub _
  simp only [dₜ, paraboloid]
  rw [H.deriv]
  ring

/-- `ΔₓP = -2d/ρ²`. -/
theorem lapₓ_paraboloid (p : E d × ℝ) : lapₓ (paraboloid x₀ t₁ ρ κ) p = -(2 * d / ρ ^ 2) := by
  have hfun : (fun y : E d ↦ paraboloid x₀ t₁ ρ κ (y, p.2)) =
      fun y ↦ (-(ρ ^ 2)⁻¹) * ‖y - x₀‖ ^ 2 + (κ - 2 * d * (p.2 - t₁) / ρ ^ 2) := by
    funext y
    simp only [paraboloid]
    ring
  rw [lapₓ, hfun, laplacian_const_mul_add_const (g := fun y : E d ↦ ‖y - x₀‖ ^ 2)
      ((contDiff_norm_sq ℝ).comp
      (contDiff_id.sub contDiff_const)).contDiffAt,
    laplacian_norm_sub_sq, finrank_euclideanSpace_fin]
  ring

/-- `∇ₓP = -(2/ρ²)(x - x₀)`. -/
theorem gradₓ_paraboloid (p : E d × ℝ) :
    gradₓ (paraboloid x₀ t₁ ρ κ) p = -(2 / ρ ^ 2) • (p.1 - x₀) := by
  have hfun : (fun y : E d ↦ paraboloid x₀ t₁ ρ κ (y, p.2)) =
      fun y ↦ (-(ρ ^ 2)⁻¹) * ‖y - x₀‖ ^ 2 + (κ - 2 * d * (p.2 - t₁) / ρ ^ 2) := by
    funext y
    simp only [paraboloid]
    ring
  rw [gradₓ, hfun, gradient_const_mul_add_const (g := fun y : E d ↦ ‖y - x₀‖ ^ 2)
      ((hasFDerivAt_norm_sub_sq x₀ p.1).differentiableAt), gradient_norm_sub_sq, smul_smul]
  congr 1
  ring

/-- The paraboloid `P` is caloric: `∂ₜP - ΔₓP = 0`. -/
theorem dₜ_sub_lapₓ_paraboloid (p : E d × ℝ) :
    dₜ (paraboloid x₀ t₁ ρ κ) p - lapₓ (paraboloid x₀ t₁ ρ κ) p = 0 := by
  rw [dₜ_paraboloid, lapₓ_paraboloid, sub_self]

variable {x₀ t₁ ρ κ}

/-- For `t ≥ t₁`, `P ≤ κ`. -/
theorem paraboloid_le {p : E d × ℝ} (ht : t₁ ≤ p.2) : paraboloid x₀ t₁ ρ κ p ≤ κ := by
  have h1 : 0 ≤ ‖p.1 - x₀‖ ^ 2 / ρ ^ 2 := by positivity
  have h2 : 0 ≤ 2 * d * (p.2 - t₁) / ρ ^ 2 := by
    have : 0 ≤ p.2 - t₁ := sub_nonneg.2 ht
    positivity
  simp only [paraboloid_apply]
  linarith

/-- For `t ≥ t₁` and `|x - x₀| ≥ ρ > 0`, `P ≤ κ - 1`. -/
theorem paraboloid_le_sub_one (hρ : 0 < ρ) {p : E d × ℝ} (ht : t₁ ≤ p.2)
    (hx : ρ ≤ ‖p.1 - x₀‖) : paraboloid x₀ t₁ ρ κ p ≤ κ - 1 := by
  have h1 : 1 ≤ ‖p.1 - x₀‖ ^ 2 / ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hρ.le hx 2
  have h2 : 0 ≤ 2 * d * (p.2 - t₁) / ρ ^ 2 := by
    have : 0 ≤ p.2 - t₁ := sub_nonneg.2 ht
    positivity
  simp only [paraboloid_apply]
  linarith

/-- The value on the axis: `P(x₀, t) = κ - 2d(t - t₁)/ρ²`. -/
theorem paraboloid_center (t : ℝ) :
    paraboloid x₀ t₁ ρ κ (x₀, t) = κ - 2 * d * (t - t₁) / ρ ^ 2 := by
  simp [paraboloid_apply]

end Barriers

end BernoulliComparison
