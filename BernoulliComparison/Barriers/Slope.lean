/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barriers.Radial
public import BernoulliComparison.Touching.Classes

/-!
# Slope bounds for touching super- and subsolutions

This file proves the supersolution slope bound `slope_super` and its static subsolution dual
`slope_sub_static` (the case `M = 0`, at the end of the file), both with the same quadratic-profile
test function.

## Main results

* `slope_super`: if `v` satisfies `TSuper(O, v, c)` and grows at least like
  `β (R(t) - |x - z₀|)₊` with `β > c` on a closed backward cylinder `N ⊆ O` below `z̄ = (x̄, t̄)`,
  where `R(t) = R₀ - M (t̄ - t)` and `R₀ = |x̄ - z₀| > 0`, then `v(z̄) > 0`.
* `slope_sub_static`: if `u` satisfies `TSub(O, E, u, c)`, `E ∩ N` lies outside `B_{R₀}(z₀)`,
  `u ≤ β (|x - z₀| - R₀)₊` on `E ∩ N` with `β < c`, and `u(z̄) ≥ 0`, then `z̄ ∉ E`.

## Proof of `slope_super`

Suppose `v(z̄) = 0` (the growth hypothesis gives `v ≥ 0` on `N`). Put
`w(x, t) := R(t) - |x - z₀|`, so `w(z̄) = 0`, and test with
`φ := g(w)`, `g(s) := β' s + A s²`, `β' := (c + β) / 2`,
`2A := β' (|M| + |d - 1| / R₀) + 1`.

* Domination: `g(s) ≤ β s₊` as soon as `A |s| ≤ min (β - β') β'` (`slopeProfile_le`); `w` is
  Lipschitz in `(x, t)` near `z̄`, so this holds on a small cylinder `Q_r(z̄) ⊆ N`, where
  `φ ≤ β w₊ ≤ v`.
* At `z̄`: `∂ₜφ = β' M`, `Δₓφ = 2A - (d - 1) β' / R₀`, so `∂ₜφ - Δₓφ ≤ -1 < 0`, and
  `|∇ₓφ| = β' > c`. Both alternatives of `TSuper` fail.

`φ` is the space-time radial profile `radialProfile g (-1) R z₀` of `Barriers/Radial.lean`.

No dilation of space (`ξ = η(t) |x - z₀|`) is needed, because the growth hypothesis is only used
on a small neighbourhood of `z̄`. The statement does not assume `O` parabolically open or `v`
continuous on `O`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

namespace Barriers

/-! ### The quadratic profile -/

/-- The profile `g(s) = β s + A s²` of the slope barrier. -/
noncomputable def slopeProfile (β A : ℝ) : ℝ → ℝ := fun s ↦ β * s + A * s ^ 2

variable {β A : ℝ}

theorem contDiff_slopeProfile {n : WithTop ℕ∞} : ContDiff ℝ n (slopeProfile β A) :=
  (contDiff_const.mul contDiff_id).add (contDiff_const.mul (contDiff_id.pow 2))

theorem hasDerivAt_slopeProfile (s : ℝ) :
    HasDerivAt (slopeProfile β A) (β + 2 * A * s) s := by
  have := ((hasDerivAt_id s).const_mul β).add ((hasDerivAt_pow 2 s).const_mul A)
  convert this using 1
  · rfl
  simp; ring

theorem deriv_slopeProfile : deriv (slopeProfile β A) = fun s ↦ β + 2 * A * s :=
  funext fun s ↦ (hasDerivAt_slopeProfile s).deriv

theorem deriv_deriv_slopeProfile : deriv (deriv (slopeProfile β A)) = fun _ ↦ 2 * A := by
  rw [deriv_slopeProfile]
  funext s
  have := ((hasDerivAt_id s).const_mul (2 * A)).const_add β
  exact this.deriv.trans (mul_one _)

/-- **Domination.** If `A |s| ≤ min (β - β') β'`, then `β' s + A s² ≤ β s₊`. -/
theorem slopeProfile_le {β' s : ℝ} (h₁ : A * |s| ≤ β - β') (h₂ : A * |s| ≤ β') :
    slopeProfile β' A s ≤ β * max s 0 := by
  simp only [slopeProfile]
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs] at h₁
    rw [max_eq_left hs]
    nlinarith [mul_le_mul_of_nonneg_left h₁ hs]
  · rw [abs_of_neg hs] at h₂
    rw [max_eq_right hs.le]
    nlinarith [mul_le_mul_of_nonneg_left h₂ (neg_nonneg.2 hs.le)]

/-! ### The slope bound -/

/-- Supersolution slope bound. Let `c > 0`, `TSuper(O, v, c)`,
`z̄ = (x̄, t̄)`, `z₀ ∈ ℝᵈ` with `R₀ := |x̄ - z₀| > 0`, `M ∈ ℝ`, `R(t) := R₀ - M (t̄ - t)`,
`ς, τ > 0` with `N := B̄_ς(x̄) × [t̄ - τ, t̄] ⊆ O`. If `v ≥ β (R(t) - |x - z₀|)₊` on `N` for
some `β > c`, then `v(z̄) > 0`.

The set `O` need not be parabolically open and `v` need not be continuous on `O`. -/
theorem slope_super {O : Set (E d × ℝ)} {v : E d × ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hv : TouchSuper O v fun _ ↦ c) {xb z₀ : E d} {tb : ℝ} (hR₀ : 0 < ‖xb - z₀‖) (M : ℝ)
    {ς τ β : ℝ} (hς : 0 < ς) (hτ : 0 < τ) (hN : closedBall xb ς ×ˢ Icc (tb - τ) tb ⊆ O)
    (hβ : c < β)
    (hvN : ∀ q ∈ closedBall xb ς ×ˢ Icc (tb - τ) tb,
      β * max (‖xb - z₀‖ - M * (tb - q.2) - ‖q.1 - z₀‖) 0 ≤ v q) :
    0 < v (xb, tb) := by
  set R₀ := ‖xb - z₀‖ with hR₀def
  have hmemN : (xb, tb) ∈ closedBall xb ς ×ˢ Icc (tb - τ) tb := by
    simp [hς.le, hτ.le]
  have hv0 : 0 ≤ v (xb, tb) := by simpa [hR₀def] using hvN _ hmemN
  refine lt_of_le_of_ne hv0 fun hv0' ↦ ?_
  -- constants
  set β' := (c + β) / 2 with hβ'
  have hβ'pos : 0 < β' := by rw [hβ']; linarith
  set A := (β' * (|M| + |(d : ℝ) - 1| / R₀) + 1) / 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set m := min (β - β') β' with hm
  have hmpos : 0 < m := lt_min (by rw [hβ']; linarith) hβ'pos
  set r := min (min 1 ς) (min τ (m / (A * (|M| + 1)))) with hr
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hrς : r ≤ ς := (min_le_left _ _).trans (min_le_right _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have hrm : r ≤ m / (A * (|M| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hrpos : 0 < r := lt_min (lt_min one_pos hς) (lt_min hτ (by positivity))
  -- the barrier
  set b : ℝ → ℝ := fun t ↦ R₀ - M * (tb - t) with hb
  set φ : E d × ℝ → ℝ := radialProfile (slopeProfile β' A) (fun _ ↦ -1) b z₀ with hφ
  have hφw : ∀ q : E d × ℝ,
      φ q = slopeProfile β' A (R₀ - M * (tb - q.2) - ‖q.1 - z₀‖) := fun q ↦ by
    simp only [hφ, radialProfile_apply, hb]
    ring_nf
  have hxb : xb ≠ z₀ := fun h ↦ by
    rw [hR₀def, h, sub_self, norm_zero] at hR₀; exact lt_irrefl _ hR₀
  have hbd : ContDiff ℝ ∞ b :=
    contDiff_const.sub (contDiff_const.mul (contDiff_const.sub contDiff_id))
  have htest : IsTestFunAt φ (xb, tb) :=
    ⟨{q | q.1 ≠ z₀}, isOpen_setOf_fst_ne z₀, hxb,
      contDiffOn_radialProfile contDiff_slopeProfile contDiff_const hbd⟩
  -- domination on `Q_r(z̄)`
  have hcross : CrossesFromBelow O v φ (xb, tb) := by
    refine ⟨hN hmemN, by rw [← hv0', hφw]; simp [slopeProfile, hR₀def], r, hrpos, fun q hq ↦ ?_⟩
    obtain ⟨hx, ht1, ht2⟩ := mem_parCyl.1 hq.2
    have hr2 : r ^ 2 ≤ r := by nlinarith
    have hqN : q ∈ closedBall xb ς ×ˢ Icc (tb - τ) tb :=
      ⟨mem_closedBall.2 (hx.le.trans hrς), by simp only at ht1 ht2 ⊢; constructor <;> linarith⟩
    refine le_trans ?_ (hvN q hqN)
    rw [hφw]
    have hw : |R₀ - M * (tb - q.2) - ‖q.1 - z₀‖| ≤ (|M| + 1) * r := by
      have h1 : |R₀ - ‖q.1 - z₀‖| ≤ r := by
        refine (abs_norm_sub_norm_le _ _).trans ?_
        rw [sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm]
        exact hx.le
      have h2 : |M * (tb - q.2)| ≤ |M| * r := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ tb - q.2)]
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      calc |R₀ - M * (tb - q.2) - ‖q.1 - z₀‖|
          = |(R₀ - ‖q.1 - z₀‖) - M * (tb - q.2)| := by ring_nf
        _ ≤ |R₀ - ‖q.1 - z₀‖| + |M * (tb - q.2)| := abs_sub _ _
        _ ≤ (|M| + 1) * r := by linarith
    have hAw : A * |R₀ - M * (tb - q.2) - ‖q.1 - z₀‖| ≤ m := by
      calc _ ≤ A * ((|M| + 1) * r) := mul_le_mul_of_nonneg_left hw hApos.le
        _ = A * (|M| + 1) * r := by ring
        _ ≤ A * (|M| + 1) * (m / (A * (|M| + 1))) :=
          mul_le_mul_of_nonneg_left hrm (by positivity)
        _ = m := by field_simp
    exact slopeProfile_le (hAw.trans (min_le_left _ _)) (hAw.trans (min_le_right _ _))
  -- derivatives at `z̄`
  have hξ : (fun _ : ℝ ↦ (-1 : ℝ)) tb * ‖xb - z₀‖ + b tb = 0 := by simp [hb, hR₀def]
  have hdiff : DifferentiableAt ℝ (slopeProfile β' A)
      ((fun _ : ℝ ↦ (-1 : ℝ)) (xb, tb).2 * ‖(xb, tb).1 - z₀‖ + b (xb, tb).2) :=
    (hasDerivAt_slopeProfile _).differentiableAt
  have hbder : HasDerivAt b M tb := by
    have := (((hasDerivAt_id tb).const_sub tb).const_mul M).const_sub R₀
    simpa [hb] using this
  have hdt : dₜ φ (xb, tb) = β' * M := by
    rw [hφ, dₜ_radialProfile (p := (xb, tb)) hdiff (hasDerivAt_const _ _) hbder]
    simp only at hξ ⊢
    rw [hξ, deriv_slopeProfile]
    ring
  have hlap : lapₓ φ (xb, tb) = 2 * A - ((d : ℝ) - 1) * β' / R₀ := by
    rw [hφ, lapₓ_radialProfile (p := (xb, tb)) contDiff_slopeProfile.contDiffAt hxb]
    simp only at hξ ⊢
    rw [hξ, deriv_deriv_slopeProfile, deriv_slopeProfile]
    ring
  have hgrad : ‖gradₓ φ (xb, tb)‖ = β' := by
    rw [hφ, norm_gradₓ_radialProfile (p := (xb, tb)) hdiff hxb]
    simp only at hξ ⊢
    rw [hξ, deriv_slopeProfile]
    simp [abs_of_pos hβ'pos]
  -- both alternatives of `TSuper` fail
  rcases hv _ (hN hmemN) φ htest hcross with hH | ⟨-, hQ⟩
  · rw [hdt, hlap] at hH
    have h1 : β' * M ≤ β' * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) hβ'pos.le
    have h2 : ((d : ℝ) - 1) * β' / R₀ ≤ |(d : ℝ) - 1| * β' / R₀ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hβ'pos.le) hR₀.le
    have h3 : 2 * A = β' * |M| + |(d : ℝ) - 1| * β' / R₀ + 1 := by
      rw [hA]; field_simp
    linarith
  · rw [hgrad] at hQ
    simp only at hQ
    rw [hβ'] at hQ
    linarith

/-! ### The static subsolution slope bound -/

/-- Static subsolution slope bound (the case `M = 0`). Let
`TSub(O, E, u, c)`, `z̄ = (x̄, t̄)`, `z₀ ∈ ℝᵈ` with `R₀ := |x̄ - z₀| > 0`, `ς, τ > 0` with
`N := B̄_ς(x̄) × [t̄ - τ, t̄] ⊆ O`, and `0 ≤ β < c`. If (i) `E ∩ N ⊆ {|x - z₀| ≥ R₀}` and (ii)
`u ≤ β (|x - z₀| - R₀)₊` on `E ∩ N`, with `u(z̄) ≥ 0`, then `z̄ ∉ E`.

Proof: otherwise `φ := f(|x - z₀|)`, `f(ξ) = β' (ξ - R₀) - (γ / 2) (ξ - R₀)²`,
`β' = (c + β) / 2`, `γ = (d - 1) β' / R₀ + 1`, touches `u` from above in `E` at `z̄`, with
`φ(z̄) = 0`, `|∇φ(z̄)| = β' < c` and `(∂ₜ - Δ)φ(z̄) = 1 > 0`.

The set `O` need not be parabolically open, `c > 0` is implied by `0 ≤ β < c`, only `u(z̄) ≥ 0`
(not `u ≥ 0` on `N`) is assumed, and the upper bound (ii) is only needed on `E ∩ N`. -/
theorem slope_sub_static {O Eset : Set (E d × ℝ)} {u : E d × ℝ → ℝ} {c : ℝ}
    (hu : TouchSub O Eset u fun _ ↦ c) {xb z₀ : E d} {tb : ℝ} (hR₀ : 0 < ‖xb - z₀‖)
    {ς τ β : ℝ} (hς : 0 < ς) (hτ : 0 < τ) (hN : closedBall xb ς ×ˢ Icc (tb - τ) tb ⊆ O)
    (hβ0 : 0 ≤ β) (hβ : β < c)
    (hEN : ∀ q ∈ Eset ∩ closedBall xb ς ×ˢ Icc (tb - τ) tb, ‖xb - z₀‖ ≤ ‖q.1 - z₀‖)
    (huN : ∀ q ∈ Eset ∩ closedBall xb ς ×ˢ Icc (tb - τ) tb,
      u q ≤ β * max (‖q.1 - z₀‖ - ‖xb - z₀‖) 0)
    (hu0 : 0 ≤ u (xb, tb)) :
    (xb, tb) ∉ Eset := by
  intro hE
  set R₀ := ‖xb - z₀‖ with hR₀def
  have hmemN : (xb, tb) ∈ closedBall xb ς ×ˢ Icc (tb - τ) tb := by
    simp [hς.le, hτ.le]
  have hu0' : u (xb, tb) = 0 := le_antisymm (by simpa [hR₀def] using huN _ ⟨hE, hmemN⟩) hu0
  -- constants
  set β' := (c + β) / 2 with hβ'
  have hβ'pos : 0 < β' := by rw [hβ']; linarith
  set γ := ((d : ℝ) - 1) * β' / R₀ + 1 with hγ
  set δ := (c - β) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set r := min (min 1 ς) (min τ (δ / (|γ| + 1))) with hr
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hrς : r ≤ ς := (min_le_left _ _).trans (min_le_right _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ / (|γ| + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hrpos : 0 < r := lt_min (lt_min one_pos hς) (lt_min hτ (by positivity))
  -- the barrier
  set φ : E d × ℝ → ℝ :=
    radialProfile (slopeProfile β' (-(γ / 2))) (fun _ ↦ 1) (fun _ ↦ -R₀) z₀ with hφ
  have hφw : ∀ q : E d × ℝ, φ q = slopeProfile β' (-(γ / 2)) (‖q.1 - z₀‖ - R₀) := fun q ↦ by
    simp only [hφ, radialProfile_apply]
    ring_nf
  have hxb : xb ≠ z₀ := fun h ↦ by
    rw [hR₀def, h, sub_self, norm_zero] at hR₀; exact lt_irrefl _ hR₀
  have htest : IsTestFunAt φ (xb, tb) :=
    ⟨{q | q.1 ≠ z₀}, isOpen_setOf_fst_ne z₀, hxb,
      contDiffOn_radialProfile contDiff_slopeProfile contDiff_const contDiff_const⟩
  -- domination on `E ∩ Q_r(z̄)`
  have hcross : CrossesFromAbove Eset u φ (xb, tb) := by
    refine ⟨hE, by rw [hu0', hφw]; simp [slopeProfile, hR₀def], r, hrpos, fun q hq ↦ ?_⟩
    obtain ⟨hx, ht1, ht2⟩ := mem_parCyl.1 hq.2
    have hr2 : r ^ 2 ≤ r := by nlinarith
    have hqN : q ∈ closedBall xb ς ×ˢ Icc (tb - τ) tb :=
      ⟨mem_closedBall.2 (hx.le.trans hrς), by simp only at ht1 ht2 ⊢; constructor <;> linarith⟩
    have hs0 : 0 ≤ ‖q.1 - z₀‖ - R₀ := sub_nonneg.2 (hEN q ⟨hq.1, hqN⟩)
    have hsr : ‖q.1 - z₀‖ - R₀ ≤ r := by
      have := norm_sub_norm_le (q.1 - z₀) (xb - z₀)
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm q.1 xb] at this
      linarith [hx.le]
    refine (huN q ⟨hq.1, hqN⟩).trans ?_
    rw [hφw, max_eq_left hs0]
    simp only [slopeProfile]
    set s := ‖q.1 - z₀‖ - R₀
    have hγs : γ / 2 * s ≤ δ := by
      have h1 : γ * s ≤ |γ| * r := mul_le_mul (le_abs_self γ) hsr hs0 (abs_nonneg γ)
      have h2 : |γ| * r ≤ δ := by
        calc |γ| * r ≤ (|γ| + 1) * (δ / (|γ| + 1)) :=
              mul_le_mul (by linarith) hrδ hrpos.le (by positivity)
          _ = δ := by field_simp
      linarith
    have : β' - β = δ := by rw [hβ', hδ]; ring
    nlinarith [mul_le_mul_of_nonneg_left hγs hs0]
  -- derivatives at `z̄`
  have hξ : (fun _ : ℝ ↦ (1 : ℝ)) tb * ‖xb - z₀‖ + (fun _ : ℝ ↦ -R₀) tb = 0 := by
    simp [hR₀def]
  have hdiff : DifferentiableAt ℝ (slopeProfile β' (-(γ / 2)))
      ((fun _ : ℝ ↦ (1 : ℝ)) (xb, tb).2 * ‖(xb, tb).1 - z₀‖ + (fun _ : ℝ ↦ -R₀) (xb, tb).2) :=
    (hasDerivAt_slopeProfile _).differentiableAt
  have hdt : dₜ φ (xb, tb) = 0 := by
    rw [hφ, dₜ_radialProfile (p := (xb, tb)) hdiff (hasDerivAt_const _ _) (hasDerivAt_const _ _)]
    ring
  have hlap : lapₓ φ (xb, tb) = -1 := by
    rw [hφ, lapₓ_radialProfile (p := (xb, tb)) contDiff_slopeProfile.contDiffAt hxb]
    simp only at hξ ⊢
    rw [hξ, deriv_deriv_slopeProfile, deriv_slopeProfile, hγ, ← hR₀def]
    field_simp
    ring
  have hgrad : ‖gradₓ φ (xb, tb)‖ = β' := by
    rw [hφ, norm_gradₓ_radialProfile (p := (xb, tb)) hdiff hxb]
    simp only at hξ ⊢
    rw [hξ, deriv_slopeProfile]
    simp [abs_of_pos hβ'pos]
  -- both alternatives of `TSub` fail
  rcases hu _ ⟨hE, hN hmemN⟩ φ htest hcross with hH | ⟨-, hQ⟩
  · rw [hdt, hlap] at hH
    linarith
  · rw [hgrad] at hQ
    simp only at hQ
    rw [hβ'] at hQ
    linarith

end Barriers

end BernoulliComparison
