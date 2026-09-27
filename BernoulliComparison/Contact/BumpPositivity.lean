/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Heat.Comparison
public import BernoulliComparison.Barriers.Paraboloid
public import BernoulliComparison.Touching.ClassBridge

/-!
# Bump positivity

Let `w` be continuous on `O` with
`Supercal({w > 0} ∩ O, w)`, and let `B̄_ρ(x₀) × [t₁, t₂] ⊆ O` with `w > 0` on
`B̄_ρ(x₀) × [t₁, t₂)` and `4d (t₂ - t₁) ≤ ρ²`. Then `w(x₀, t₂) ≥ σ/2` for every lower bound
`σ ≥ 0` of `w` on the bottom face; in particular `w(x₀, t₂) > 0`.

The barrier is `σ P` with the caloric paraboloid `P` of `Barriers/Paraboloid.lean` (`κ = 1`),
compared with `w` on `B_ρ(x₀) × (t₁, t₂)` by `Heat.domain_comparison_super` (boundary data only
for `t < t₂`; the top face is reached through the penalization, so no limit `δ → 0` is needed).

The time condition `t₂ ≤ t₁ + ρ²/(4d)` is written `4d (t₂ - t₁) ≤ ρ²` (no division by `d`), and
`O` need not be parabolically open.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

namespace Contact

variable {d : ℕ}

/-- Bump positivity: let `w` be continuous on `O` with `Supercal({w > 0} ∩ O, w)`,
`ρ > 0`, `t₁ < t₂` with `4d (t₂ - t₁) ≤ ρ²`, `B̄_ρ(x₀) × [t₁, t₂] ⊆ O`, and `w > 0` on
`B̄_ρ(x₀) × [t₁, t₂)`. If `0 ≤ σ ≤ w` on the bottom face `B̄_ρ(x₀) × {t₁}`, then
`σ / 2 ≤ w(x₀, t₂)`. -/
theorem bump_positivity {O : Set (E d × ℝ)} {w : E d × ℝ → ℝ} (hw : ContinuousOn w O)
    (hsup : IsSupercal (posSetP w O) w) {x₀ : E d} {ρ t₁ t₂ σ : ℝ} (hρ : 0 < ρ)
    (ht : t₁ < t₂) (htd : 4 * d * (t₂ - t₁) ≤ ρ ^ 2)
    (hsub : closedBall x₀ ρ ×ˢ Icc t₁ t₂ ⊆ O)
    (hpos : ∀ p ∈ closedBall x₀ ρ ×ˢ Ico t₁ t₂, 0 < w p)
    (hσ0 : 0 ≤ σ) (hσ : ∀ y ∈ closedBall x₀ ρ, σ ≤ w (y, t₁)) :
    σ / 2 ≤ w (x₀, t₂) := by
  set Ω : Set (E d × ℝ) := ball x₀ ρ ×ˢ Ioo t₁ t₂ with hΩ
  set b : E d × ℝ → ℝ := σ • Barriers.paraboloid x₀ t₁ ρ 1 with hb
  have hclΩ : closure Ω = closedBall x₀ ρ ×ˢ Icc t₁ t₂ := by
    rw [hΩ, Heat.closure_prod_Ioo ht, closure_ball x₀ hρ.ne']
  have hΩO : Ω ⊆ posSetP w O := fun p hp ↦
    ⟨hsub ⟨ball_subset_closedBall hp.1, Ioo_subset_Icc_self hp.2⟩,
      hpos p ⟨ball_subset_closedBall hp.1, Ioo_subset_Ico_self hp.2⟩⟩
  have hΩo : IsOpen Ω := isOpen_ball.prod isOpen_Ioo
  have hsupΩ : IsCaloricSuper Ω w := (hsup.restrict hΩO hΩo.isParOpen).isCaloricSuper
  have hbsmooth : ContDiff ℝ ∞ b := contDiff_const.smul (Barriers.contDiff_paraboloid _ _ _ _)
  have hcomp := Heat.domain_comparison_super (T₁ := t₂) (b := b) hΩo
    (isBounded_ball.prod (Metric.isBounded_Ioo t₁ t₂)) (fun p hp ↦ hp.2.2) hsupΩ
    (by rw [hclΩ]; exact hw.mono hsub) hbsmooth.continuous.continuousOn hbsmooth.contDiffOn
    (fun p _ ↦ by
      rw [hb, dₜ_smul, lapₓ_smul ((Barriers.contDiff_paraboloid _ _ _ _).of_le le_top),
        ← mul_sub, Barriers.dₜ_sub_lapₓ_paraboloid, mul_zero])
    (fun p hp hpt ↦ by
      have hpb := Heat.mem_parBdry_of_mem_frontier ht hp hpt
      rcases hpb with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
      · rw [closure_ball x₀ hρ.ne'] at hp1
        rw [mem_singleton_iff] at hp2
        have hP := Barriers.paraboloid_le (x₀ := x₀) (ρ := ρ) (κ := 1) (p := p) hp2.ge
        have hwp := hσ p.1 hp1
        have : (p.1, t₁) = p := Prod.ext rfl hp2.symm
        rw [this] at hwp
        simp only [hb, Pi.smul_apply, smul_eq_mul]
        nlinarith
      · rw [frontier_ball x₀ hρ.ne', mem_sphere, dist_eq_norm] at hp1
        have hP := Barriers.paraboloid_le_sub_one (x₀ := x₀) (κ := 1) hρ hp2.1 hp1.ge
        have hwp := hpos p ⟨sphere_subset_closedBall (by rwa [mem_sphere, dist_eq_norm]),
          hp2.1, hpt⟩
        simp only [hb, Pi.smul_apply, smul_eq_mul]
        nlinarith)
  have hmem : (x₀, t₂) ∈ closure Ω := by
    rw [hclΩ]; exact ⟨mem_closedBall_self hρ.le, ht.le, le_rfl⟩
  have h := hcomp _ hmem
  simp only [hb, Pi.smul_apply, smul_eq_mul, Barriers.paraboloid_center] at h
  have hq : 2 * (d : ℝ) * (t₂ - t₁) / ρ ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  nlinarith

/-- Bump positivity, positivity form: under the hypotheses of `bump_positivity`
(without `σ`), `w(x₀, t₂) > 0`. -/
theorem bump_positivity_pos {O : Set (E d × ℝ)} {w : E d × ℝ → ℝ} (hw : ContinuousOn w O)
    (hsup : IsSupercal (posSetP w O) w) {x₀ : E d} {ρ t₁ t₂ : ℝ} (hρ : 0 < ρ)
    (ht : t₁ < t₂) (htd : 4 * d * (t₂ - t₁) ≤ ρ ^ 2)
    (hsub : closedBall x₀ ρ ×ˢ Icc t₁ t₂ ⊆ O)
    (hpos : ∀ p ∈ closedBall x₀ ρ ×ˢ Ico t₁ t₂, 0 < w p) :
    0 < w (x₀, t₂) := by
  have hc : ContinuousOn (fun y : E d ↦ w (y, t₁)) (closedBall x₀ ρ) :=
    hw.comp (continuous_id.prodMk continuous_const).continuousOn
      fun y hy ↦ hsub ⟨hy, le_rfl, ht.le⟩
  obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall x₀ ρ).exists_isMinOn
    (nonempty_closedBall.mpr hρ.le) hc
  have hσ : 0 < w (y₀, t₁) := hpos _ ⟨hy₀, le_rfl, ht⟩
  have := bump_positivity hw hsup hρ ht htd hsub hpos hσ.le fun y hy ↦ isMinOn_iff.mp hmin y hy
  linarith

end Contact

end BernoulliComparison
