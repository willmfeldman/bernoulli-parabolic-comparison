/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Heat.Penalization

/-!
# Caloric comparison on space-time domains

A viscosity subcaloric function (touching form, `IsCaloricSub`) lies below a barrier which is
continuous on `closure Ω`, `C^∞` in `Ω` and supercaloric there, as soon as it does on
`frontier Ω ∩ {t < T₁}`; and dually.

The statements do not assume `d ≥ 1`, `Ω ≠ ∅`, or a lower time bound: only `Ω ⊆ {t < T₁}` is
used.

The barrier is only `C^∞` on `Ω`, while `IsCaloricSub` tests with globally `C^∞` functions; the
localization of `Heat/Local.lean` (extension by a smooth bump) bridges the two.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

namespace Heat

variable {Ω : Set (E d × ℝ)} {T₁ : ℝ} {b : E d × ℝ → ℝ}

/-- **Domain comparison for subcaloric functions.** Let
`Ω ⊆ {t < T₁}` be open and bounded, `W` continuous on `closure Ω` and subcaloric in `Ω`, and
`b` continuous on `closure Ω`, `C^∞` on `Ω` with `∂ₜb - Δb ≥ 0` on `Ω`. If `W ≤ b` on
`frontier Ω ∩ {t < T₁}`, then `W ≤ b` on `closure Ω`. -/
theorem domain_comparison_sub {W : E d × ℝ → ℝ} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩT : ∀ p ∈ Ω, p.2 < T₁) (hW : IsCaloricSub Ω W) (hWc : ContinuousOn W (closure Ω))
    (hbc : ContinuousOn b (closure Ω)) (hb : ContDiffOn ℝ ∞ b Ω)
    (hheat : ∀ p ∈ Ω, 0 ≤ dₜ b p - lapₓ b p)
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → W p ≤ b p) :
    ∀ p ∈ closure Ω, W p ≤ b p := by
  set F : E d × ℝ → ℝ := fun q ↦ W q - b q with hFdef
  have hFc : ContinuousOn F (closure Ω) := hWc.sub hbc
  suffices h : ∀ p ∈ closure Ω, F p ≤ 0 from fun p hp ↦ sub_nonpos.1 (h p hp)
  refine nonpos_on_closure_of_penalized hΩT hFc fun ε hε q₁ hq₁ ↦ ?_
  by_contra hpos
  rw [not_le] at hpos
  obtain ⟨p, hpΩ, -, hmax⟩ := exists_isMaxOn_penalized hΩo hΩb hΩT hFc
    (fun p hp hpT ↦ sub_nonpos.2 (hbdry p hp hpT)) hε hq₁ hpos
  have hΩsub : Ω ⊆ {q : E d × ℝ | q.2 < T₁} := hΩT
  have hpen : ContDiffOn ℝ ∞ (penalty T₁) Ω := (contDiffOn_penalty T₁).mono hΩsub
  -- the penalized barrier plus a constant crosses `W` from above in `Ω` at `p`
  have hcross := CrossesFromAbove.of_local_max_add_const (S := Ω) (u := W)
    (φ := fun q ↦ b q + ε * penalty T₁ q) hpΩ one_pos fun q hq ↦ by
      have := hmax q hq.1
      simp only [hFdef] at this
      linarith
  have hfun : (fun q ↦ b q + ε * penalty T₁ q + (W p - (b p + ε * penalty T₁ p))) =
      fun q ↦ b q + (ε * penalty T₁ q + (W p - (b p + ε * penalty T₁ p))) :=
    funext fun q ↦ by ring
  rw [hfun] at hcross
  have hsmooth : ContDiffOn ℝ ∞
      (fun q ↦ b q + (ε * penalty T₁ q + (W p - (b p + ε * penalty T₁ p)))) Ω :=
    hb.add ((contDiffOn_const.mul hpen).add contDiffOn_const)
  have h1 := hW.heat_nonpos_of_contDiffOn hΩo hpΩ hsmooth hcross
  rw [dₜ_sub_lapₓ_add_mul_add_of_contDiffOn hΩo hpΩ hb hpen, dₜ_sub_lapₓ_penalty (hΩT p hpΩ)]
    at h1
  have h2 := hheat p hpΩ
  have h3 : 0 < ε * ((T₁ - p.2) ^ 2)⁻¹ :=
    mul_pos hε (inv_pos.2 (pow_pos (sub_pos.2 (hΩT p hpΩ)) 2))
  linarith

/-- **Domain comparison for supercaloric functions.** Let
`Ω ⊆ {t < T₁}` be open and bounded, `v` continuous on `closure Ω` and supercaloric in `Ω`, and
`b` continuous on `closure Ω`, `C^∞` on `Ω` with `∂ₜb - Δb ≤ 0` on `Ω`. If `b ≤ v` on
`frontier Ω ∩ {t < T₁}`, then `b ≤ v` on `closure Ω`. -/
theorem domain_comparison_super {v : E d × ℝ → ℝ} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩT : ∀ p ∈ Ω, p.2 < T₁) (hv : IsCaloricSuper Ω v)
    (hvc : ContinuousOn v (closure Ω)) (hbc : ContinuousOn b (closure Ω))
    (hb : ContDiffOn ℝ ∞ b Ω) (hheat : ∀ p ∈ Ω, dₜ b p - lapₓ b p ≤ 0)
    (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → b p ≤ v p) :
    ∀ p ∈ closure Ω, b p ≤ v p := by
  set F : E d × ℝ → ℝ := fun q ↦ b q - v q with hFdef
  have hFc : ContinuousOn F (closure Ω) := hbc.sub hvc
  suffices h : ∀ p ∈ closure Ω, F p ≤ 0 from fun p hp ↦ sub_nonpos.1 (h p hp)
  refine nonpos_on_closure_of_penalized hΩT hFc fun ε hε q₁ hq₁ ↦ ?_
  by_contra hpos
  rw [not_le] at hpos
  obtain ⟨p, hpΩ, -, hmax⟩ := exists_isMaxOn_penalized hΩo hΩb hΩT hFc
    (fun p hp hpT ↦ sub_nonpos.2 (hbdry p hp hpT)) hε hq₁ hpos
  have hΩsub : Ω ⊆ {q : E d × ℝ | q.2 < T₁} := hΩT
  have hpen : ContDiffOn ℝ ∞ (penalty T₁) Ω := (contDiffOn_penalty T₁).mono hΩsub
  -- the penalized barrier plus a constant crosses `v` from below in `Ω` at `p`
  have hcross := CrossesFromBelow.of_local_min_add_const (S := Ω) (u := v)
    (φ := fun q ↦ b q - ε * penalty T₁ q) hpΩ one_pos fun q hq ↦ by
      have := hmax q hq.1
      simp only [hFdef] at this
      linarith
  have hfun : (fun q ↦ b q - ε * penalty T₁ q + (v p - (b p - ε * penalty T₁ p))) =
      fun q ↦ b q + (-ε * penalty T₁ q + (v p - (b p - ε * penalty T₁ p))) :=
    funext fun q ↦ by ring
  rw [hfun] at hcross
  have hsmooth : ContDiffOn ℝ ∞
      (fun q ↦ b q + (-ε * penalty T₁ q + (v p - (b p - ε * penalty T₁ p)))) Ω :=
    hb.add ((contDiffOn_const.mul hpen).add contDiffOn_const)
  have h1 := hv.heat_nonneg_of_contDiffOn hΩo hpΩ hsmooth hcross
  rw [dₜ_sub_lapₓ_add_mul_add_of_contDiffOn hΩo hpΩ hb hpen, dₜ_sub_lapₓ_penalty (hΩT p hpΩ)]
    at h1
  have h2 := hheat p hpΩ
  have h3 : 0 < ε * ((T₁ - p.2) ^ 2)⁻¹ :=
    mul_pos hε (inv_pos.2 (pow_pos (sub_pos.2 (hΩT p hpΩ)) 2))
  linarith

end Heat

end BernoulliComparison
