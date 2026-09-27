/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barriers.Radial
public import BernoulliComparison.Barriers.PolarBarrier

/-!
# Self-similar polar barriers: the radial versions

For `x* ∈ ℝᵈ`, `ℓ = λ₁ > 0`, `t* ∈ ℝ` put `y := |x - x*| - ℓ`, `s := t* - t`, `ω := √s` and

* `b₊(x, t) := B₊(y, s)` (`polarOuterRadial`), `b₋(x, t) := B₋(y, s)` (`polarInnerRadial`),

total functions on `E d × ℝ`. On the open sets (`polarOuterDomain`, `polarInnerDomain`)
`G± = {0 < s < (Aℓ/(16d))², |x - x*| > ℓ/2, ±(y - Aω) > 0}` they are `C^∞` and
`∂ₜb₊ - Δb₊ ≥ 0`, `∂ₜb₋ - Δb₋ ≤ 0` (for `0 < A ≤ 1`).

## Main statements

* `continuous_polarOuterRadial`, `continuousOn_polarInnerRadial` (on `{y ≤ Aω}`);
* `isOpen_polarOuterDomain`, `isOpen_polarInnerDomain`;
* `contDiffOn_polarOuterRadial`, `contDiffOn_polarInnerRadial`;
* `polarOuterRadial_heat`, `polarInnerRadial_heat`;
* `polar_barrier_outer`, `polar_barrier_inner`: the profile bounds of
  `Barriers/PolarBarrier.lean` together with the radial statements, bundled in the form used in
  `Polar/NorthInterior.lean` (continuity on the closed set, bounds, smoothness and the sign
  of `∂ₜ - Δ` on `G±`).

The radial computation is `dₜ_sub_lapₓ_radial_two`: for `b(x, t) = B(|x - x*| - ℓ, t* - t)`,
`(∂ₜ - Δ) b = -∂ₛB - ∂²ᵧB - (d - 1) ∂ᵧB / |x - x*|`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Laplacian

namespace BernoulliComparison

variable {d : ℕ}

namespace Barriers

/-! ### Radial calculus for `B(|x - x*| - ℓ, t* - t)` -/

section RadialTwo

variable {B By Byy Bs : ℝ → ℝ → ℝ} {ℓ tstar : ℝ} {xstar : E d} {q : E d × ℝ}

/-- **Heat operator of a radial space-time function** `b(x, t) = B(|x - x*| - ℓ, t* - t)`:
`∂ₜb - Δb = -∂ₛB - ∂²ᵧB - (d - 1) ∂ᵧB / |x - x*|` at a point with `x ≠ x*`, given the
partial derivatives of `B` at `(y, s) = (|x - x*| - ℓ, t* - q.2)`. -/
theorem dₜ_sub_lapₓ_radial_two (hx : q.1 ≠ xstar)
    (hs : HasDerivAt (fun s ↦ B (‖q.1 - xstar‖ - ℓ) s)
      (Bs (‖q.1 - xstar‖ - ℓ) (tstar - q.2)) (tstar - q.2))
    (hy : ∀ᶠ r in 𝓝 (‖q.1 - xstar‖ - ℓ),
      HasDerivAt (fun y ↦ B y (tstar - q.2)) (By r (tstar - q.2)) r)
    (hyy : HasDerivAt (fun y ↦ By y (tstar - q.2)) (Byy (‖q.1 - xstar‖ - ℓ) (tstar - q.2))
      (‖q.1 - xstar‖ - ℓ))
    (hC2 : ContDiffAt ℝ 2 (fun y ↦ B y (tstar - q.2)) (‖q.1 - xstar‖ - ℓ)) :
    dₜ (fun p : E d × ℝ ↦ B (‖p.1 - xstar‖ - ℓ) (tstar - p.2)) q -
        lapₓ (fun p : E d × ℝ ↦ B (‖p.1 - xstar‖ - ℓ) (tstar - p.2)) q =
      -Bs (‖q.1 - xstar‖ - ℓ) (tstar - q.2) - Byy (‖q.1 - xstar‖ - ℓ) (tstar - q.2) -
        ((d : ℝ) - 1) * By (‖q.1 - xstar‖ - ℓ) (tstar - q.2) / ‖q.1 - xstar‖ := by
  set ρ := ‖q.1 - xstar‖ with hρ
  set s := tstar - q.2 with hsdef
  -- time derivative
  have hdt : dₜ (fun p : E d × ℝ ↦ B (‖p.1 - xstar‖ - ℓ) (tstar - p.2)) q = -Bs (ρ - ℓ) s := by
    have ht : HasDerivAt (fun t ↦ tstar - t) (-1) q.2 := by
      simpa using (hasDerivAt_id q.2).const_sub tstar
    have := hs.comp q.2 ht
    simp only [dₜ]
    exact this.deriv.trans (by ring)
  -- spatial Laplacian, via the one-variable profile `f r = B (r - ℓ) s`
  set f : ℝ → ℝ := fun r ↦ B (r - ℓ) s with hf
  have hsub : HasDerivAt (fun r : ℝ ↦ r - ℓ) 1 ρ := (hasDerivAt_id ρ).sub_const ℓ
  have hf2 : ContDiffAt ℝ 2 f ρ := hC2.comp ρ (contDiffAt_id.sub contDiffAt_const)
  have hdf : deriv f =ᶠ[𝓝 ρ] fun r ↦ By (r - ℓ) s := by
    have hev : ∀ᶠ r in 𝓝 ρ, HasDerivAt (fun y ↦ B y s) (By (r - ℓ) s) (r - ℓ) :=
      ((continuous_sub_right ℓ).tendsto ρ).eventually hy
    filter_upwards [hev] with r hr
    have := hr.comp r ((hasDerivAt_id r).sub_const ℓ)
    rw [mul_one] at this
    exact this.deriv
  have hdf1 : deriv f ρ = By (ρ - ℓ) s := hdf.eq_of_nhds
  have hdf2 : deriv (deriv f) ρ = Byy (ρ - ℓ) s := by
    rw [hdf.deriv_eq]
    have := hyy.comp ρ hsub
    rw [mul_one] at this
    exact this.deriv
  have hlap : lapₓ (fun p : E d × ℝ ↦ B (‖p.1 - xstar‖ - ℓ) (tstar - p.2)) q =
      Byy (ρ - ℓ) s + ((d : ℝ) - 1) * By (ρ - ℓ) s / ρ := by
    have H := laplacian_radial (F := E d) (z := xstar) hf2 hx
    rw [finrank_euclideanSpace_fin, hdf1, hdf2] at H
    exact H
  rw [hdt, hlap]
  ring

end RadialTwo

/-! ### Definitions -/

/-- The radial outer barrier `b₊(x, t) = B₊(|x - x*| - ℓ, t* - t)`. -/
noncomputable def polarOuterRadial (A ℓ tstar : ℝ) (xstar : E d) : E d × ℝ → ℝ :=
  fun q ↦ polarOuter A (‖q.1 - xstar‖ - ℓ) (tstar - q.2)

/-- The radial inner barrier `b₋(x, t) = B₋(|x - x*| - ℓ, t* - t)`. -/
noncomputable def polarInnerRadial (A ℓ tstar : ℝ) (xstar : E d) : E d × ℝ → ℝ :=
  fun q ↦ polarInner A (‖q.1 - xstar‖ - ℓ) (tstar - q.2)

/-- The open set `G₊ = {0 < t* - t < (Aℓ/(16d))², |x - x*| > ℓ/2, y - A√(t* - t) > 0}`. -/
def polarOuterDomain (A ℓ tstar : ℝ) (xstar : E d) : Set (E d × ℝ) :=
  {q | 0 < tstar - q.2 ∧ tstar - q.2 < (A * ℓ / (16 * d)) ^ 2 ∧ ℓ / 2 < ‖q.1 - xstar‖ ∧
    A * √(tstar - q.2) < ‖q.1 - xstar‖ - ℓ}

/-- The open set `G₋ = {0 < t* - t < (Aℓ/(16d))², |x - x*| > ℓ/2, y - A√(t* - t) < 0}`. -/
def polarInnerDomain (A ℓ tstar : ℝ) (xstar : E d) : Set (E d × ℝ) :=
  {q | 0 < tstar - q.2 ∧ tstar - q.2 < (A * ℓ / (16 * d)) ^ 2 ∧ ℓ / 2 < ‖q.1 - xstar‖ ∧
    ‖q.1 - xstar‖ - ℓ < A * √(tstar - q.2)}

variable {A ℓ tstar : ℝ} {xstar : E d}

theorem polarOuterRadial_apply (q : E d × ℝ) :
    polarOuterRadial A ℓ tstar xstar q = polarOuter A (‖q.1 - xstar‖ - ℓ) (tstar - q.2) := rfl

theorem polarInnerRadial_apply (q : E d × ℝ) :
    polarInnerRadial A ℓ tstar xstar q = polarInner A (‖q.1 - xstar‖ - ℓ) (tstar - q.2) := rfl

/-! ### Continuity -/

theorem continuous_yst : Continuous fun q : E d × ℝ ↦ (‖q.1 - xstar‖ - ℓ, tstar - q.2) :=
  (((continuous_fst.sub continuous_const).norm).sub continuous_const).prodMk
    (continuous_const.sub continuous_snd)

/-- Continuity of `b₊` (everywhere, for `A ≥ 0`). -/
theorem continuous_polarOuterRadial (hA : 0 ≤ A) :
    Continuous (polarOuterRadial A ℓ tstar xstar) :=
  (continuous_polarOuter hA).comp continuous_yst

/-- Continuity of `b₋` on the closed set
`{|x - x*| - ℓ ≤ A √(t* - t)}` (for `A < 8`). -/
theorem continuousOn_polarInnerRadial (hA8 : A < 8) :
    ContinuousOn (polarInnerRadial A ℓ tstar xstar)
      {q | ‖q.1 - xstar‖ - ℓ ≤ A * √(tstar - q.2)} :=
  (continuousOn_polarInner hA8).comp continuous_yst.continuousOn fun _ hq ↦ hq

/-! ### The domains -/

theorem isOpen_polarOuterDomain : IsOpen (polarOuterDomain A ℓ tstar xstar) := by
  have hs : Continuous fun q : E d × ℝ ↦ tstar - q.2 := continuous_const.sub continuous_snd
  have hρ : Continuous fun q : E d × ℝ ↦ ‖q.1 - xstar‖ := (continuous_fst.sub continuous_const).norm
  exact (isOpen_lt continuous_const hs).and ((isOpen_lt hs continuous_const).and
    ((isOpen_lt continuous_const hρ).and
      (isOpen_lt (continuous_const.mul hs.sqrt) (hρ.sub continuous_const))))

theorem isOpen_polarInnerDomain : IsOpen (polarInnerDomain A ℓ tstar xstar) := by
  have hs : Continuous fun q : E d × ℝ ↦ tstar - q.2 := continuous_const.sub continuous_snd
  have hρ : Continuous fun q : E d × ℝ ↦ ‖q.1 - xstar‖ := (continuous_fst.sub continuous_const).norm
  exact (isOpen_lt continuous_const hs).and ((isOpen_lt hs continuous_const).and
    ((isOpen_lt continuous_const hρ).and
      (isOpen_lt (hρ.sub continuous_const) (continuous_const.mul hs.sqrt))))

/-- On `G±`, `16 d ω ≤ A ℓ`. -/
theorem sixteen_mul_sqrt_le {s : ℝ} (hA : 0 ≤ A) (hℓ : 0 ≤ ℓ) (hs : s < (A * ℓ / (16 * d)) ^ 2) :
    16 * d * √s ≤ A * ℓ := by
  rcases le_or_gt s 0 with hs0 | hs0
  · rw [Real.sqrt_eq_zero'.2 hs0, mul_zero]; positivity
  have hc : 0 ≤ A * ℓ / (16 * d) := by positivity
  have h1 : √s < A * ℓ / (16 * d) := by
    have := Real.sqrt_lt_sqrt hs0.le hs
    rwa [Real.sqrt_sq hc] at this
  rcases (Nat.cast_nonneg d : (0 : ℝ) ≤ d).eq_or_lt with hd | hd
  · rw [← hd, mul_zero, zero_mul]; positivity
  · rw [lt_div_iff₀ (by positivity)] at h1
    linarith

/-! ### Smoothness -/

theorem contDiffOn_polarOuterRadial (hℓ : 0 < ℓ) :
    ContDiffOn ℝ ∞ (polarOuterRadial A ℓ tstar xstar) (polarOuterDomain A ℓ tstar xstar) := by
  intro q hq
  obtain ⟨hs, -, hρ, hz⟩ := hq
  have hx : q.1 ≠ xstar := fun h ↦ by rw [h, sub_self, norm_zero] at hρ; linarith
  have hP : ‖q.1 - xstar‖ - ℓ - A * √(tstar - q.2) + √(tstar - q.2) ≠ 0 := by
    have := Real.sqrt_nonneg (tstar - q.2); linarith
  have hyst : ContDiffAt ℝ ∞ (fun q : E d × ℝ ↦ (‖q.1 - xstar‖ - ℓ, tstar - q.2)) q :=
    ((((contDiffAt_norm_sub hx).comp q contDiffAt_fst).sub contDiffAt_const).prodMk
      (contDiffAt_const.sub contDiffAt_snd))
  exact ((contDiffAt_polarOuter hs.ne' hP).comp q hyst).contDiffWithinAt

theorem contDiffOn_polarInnerRadial (hℓ : 0 < ℓ) :
    ContDiffOn ℝ ∞ (polarInnerRadial A ℓ tstar xstar) (polarInnerDomain A ℓ tstar xstar) := by
  intro q hq
  obtain ⟨hs, -, hρ, hw⟩ := hq
  have hx : q.1 ≠ xstar := fun h ↦ by rw [h, sub_self, norm_zero] at hρ; linarith
  have hP : A * √(tstar - q.2) - (‖q.1 - xstar‖ - ℓ) + √(tstar - q.2) ≠ 0 := by
    have := Real.sqrt_nonneg (tstar - q.2); linarith
  have hyst : ContDiffAt ℝ ∞ (fun q : E d × ℝ ↦ (‖q.1 - xstar‖ - ℓ, tstar - q.2)) q :=
    ((((contDiffAt_norm_sub hx).comp q contDiffAt_fst).sub contDiffAt_const).prodMk
      (contDiffAt_const.sub contDiffAt_snd))
  exact ((contDiffAt_polarInner hs.ne' hP).comp q hyst).contDiffWithinAt

/-! ### The heat inequalities -/

/-- Heat inequality for the outer radial barrier: `∂ₜb₊ - Δb₊ ≥ 0` on `G₊`, for `0 < A ≤ 1`,
`ℓ > 0`. -/
theorem polarOuterRadial_heat (hA : 0 < A) (hA1 : A ≤ 1) (hℓ : 0 < ℓ) :
    ∀ q ∈ polarOuterDomain A ℓ tstar xstar,
      0 ≤ dₜ (polarOuterRadial A ℓ tstar xstar) q - lapₓ (polarOuterRadial A ℓ tstar xstar) q := by
  intro q ⟨hs, hsτ, hρ, hz⟩
  have hx : q.1 ≠ xstar := fun h ↦ by rw [h, sub_self, norm_zero] at hρ; linarith
  set ρ := ‖q.1 - xstar‖ with hρdef
  set s := tstar - q.2 with hsdef
  have hω : 0 < √s := Real.sqrt_pos.2 hs
  have hP : ρ - ℓ - A * √s + √s ≠ 0 := by linarith
  have hPev : ∀ᶠ r in 𝓝 (ρ - ℓ), r - A * √s + √s ≠ 0 :=
    ((continuousAt_id.sub_const _).add_const _).eventually_ne hP
  have H := dₜ_sub_lapₓ_radial_two (B := polarOuter A) (By := polarOuterDy A)
    (Byy := polarOuterDyy A) (Bs := polarOuterDs A) (ℓ := ℓ) (tstar := tstar) hx
    (hasDerivAt_polarOuter_s hs hP) (hPev.mono fun r hr ↦ hasDerivAt_polarOuter_y hr)
    (hasDerivAt_polarOuterDy hP)
    ((contDiffAt_polarOuter hs.ne' hP).comp (ρ - ℓ) (contDiffAt_id.prodMk contDiffAt_const))
  rw [show polarOuterRadial A ℓ tstar xstar =
    fun p : E d × ℝ ↦ polarOuter A (‖p.1 - xstar‖ - ℓ) (tstar - p.2) from rfl, H]
  -- the one-dimensional bounds
  have h1 := polarOuter_heat hA hA1 hs hz.le
  have h2 := polarOuterDy_nonneg hA.le hs hz.le
  have h3 := polarOuterDy_le (by linarith) hs hz.le
  have h16 := sixteen_mul_sqrt_le hA.le hℓ.le hsτ
  set X := (ρ - ℓ - A * √s + √s) ^ (A / 8)
  have hX : 0 < X := Real.rpow_pos_of_pos (by linarith) _
  set Dy := polarOuterDy A (ρ - ℓ) s
  have hρpos : 0 < ρ := by linarith
  -- `(d - 1) ∂ᵧB₊ / ρ ≤ 4 d X / ℓ ≤ (A/4) X / ω`
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have k1 : ((d : ℝ) - 1) * Dy / ρ ≤ 4 * d * X / ℓ := by
    rw [div_le_div_iff₀ hρpos hℓ]
    have h' : ((d : ℝ) - 1) * Dy ≤ d * (2 * X) := by nlinarith
    have := mul_le_mul_of_nonneg_right h' hℓ.le
    have := mul_le_mul_of_nonneg_left (by linarith : ℓ ≤ 2 * ρ)
      (by positivity : (0 : ℝ) ≤ d * (2 * X))
    nlinarith
  have k2 : 4 * d * X / ℓ ≤ A / 4 * X / √s := by
    rw [div_le_div_iff₀ hℓ hω]
    nlinarith
  linarith

/-- Heat inequality for the inner radial barrier: `∂ₜb₋ - Δb₋ ≤ 0` on `G₋`, for `0 < A ≤ 1`,
`ℓ > 0`. -/
theorem polarInnerRadial_heat (hA : 0 < A) (hA1 : A ≤ 1) (hℓ : 0 < ℓ) :
    ∀ q ∈ polarInnerDomain A ℓ tstar xstar,
      dₜ (polarInnerRadial A ℓ tstar xstar) q - lapₓ (polarInnerRadial A ℓ tstar xstar) q ≤ 0 := by
  intro q ⟨hs, hsτ, hρ, hw⟩
  have hx : q.1 ≠ xstar := fun h ↦ by rw [h, sub_self, norm_zero] at hρ; linarith
  set ρ := ‖q.1 - xstar‖ with hρdef
  set s := tstar - q.2 with hsdef
  have hω : 0 < √s := Real.sqrt_pos.2 hs
  have hP : A * √s - (ρ - ℓ) + √s ≠ 0 := by linarith
  have hPev : ∀ᶠ r in 𝓝 (ρ - ℓ), A * √s - r + √s ≠ 0 :=
    ((continuousAt_const.sub continuousAt_id).add_const _).eventually_ne hP
  have H := dₜ_sub_lapₓ_radial_two (B := polarInner A) (By := polarInnerDy A)
    (Byy := polarInnerDyy A) (Bs := polarInnerDs A) (ℓ := ℓ) (tstar := tstar) hx
    (hasDerivAt_polarInner_s hs hP) (hPev.mono fun r hr ↦ hasDerivAt_polarInner_y hr)
    (hasDerivAt_polarInnerDy hP)
    ((contDiffAt_polarInner hs.ne' hP).comp (ρ - ℓ) (contDiffAt_id.prodMk contDiffAt_const))
  rw [show polarInnerRadial A ℓ tstar xstar =
    fun p : E d × ℝ ↦ polarInner A (‖p.1 - xstar‖ - ℓ) (tstar - p.2) from rfl, H]
  have h1 := polarInner_heat hA hA1 hs hw.le
  have h2 := polarInnerDy_nonpos (by linarith) hs hw.le
  have h3 := neg_le_polarInnerDy hA.le hs hw.le
  have h16 := sixteen_mul_sqrt_le hA.le hℓ.le hsτ
  set X := (A * √s - (ρ - ℓ) + √s) ^ (-(A / 8))
  have hX : 0 < X := Real.rpow_pos_of_pos (by linarith) _
  set Dy := polarInnerDy A (ρ - ℓ) s
  have hρpos : 0 < ρ := by linarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- `-(d - 1) ∂ᵧB₋ / ρ ≤ 2 d X / ℓ ≤ (11A/64) X / ω`
  have k1 : -(((d : ℝ) - 1) * Dy / ρ) ≤ 2 * d * X / ℓ := by
    rw [← neg_div, div_le_div_iff₀ hρpos hℓ]
    have h' : -(((d : ℝ) - 1) * Dy) ≤ d * X := by nlinarith
    have := mul_le_mul_of_nonneg_right h' hℓ.le
    have := mul_le_mul_of_nonneg_left (by linarith : ℓ ≤ 2 * ρ) (by positivity : (0 : ℝ) ≤ d * X)
    nlinarith
  have k2 : 2 * d * X / ℓ ≤ 11 * A / 64 * X / √s := by
    rw [div_le_div_iff₀ hℓ hω]
    have := mul_le_mul_of_nonneg_right h16 hX.le
    have : 0 ≤ A * ℓ * X := by positivity
    nlinarith
  linarith

/-! ### Bundled statements -/

/-- The outer polar barrier. Let `0 < A ≤ 1`, `ϑ = A/8`,
`ℓ = λ₁ > 0`, and `b₊(x, t) = B₊(y, s)`, `y = |x - x*| - ℓ`, `s = t* - t`, `ω = √s`. Then

* `b₊` is continuous (on all of `E d × ℝ`);
* on `Γ₊ = {y ≥ A ω}`: `z^(1+ϑ) ≤ b₊ ≤ y (y + ω)^ϑ`, `z = y - A ω`;
* `b₊` is `C^∞` on the open set `G₊` and `∂ₜb₊ - Δb₊ ≥ 0` there. -/
theorem polar_barrier_outer (hA : 0 < A) (hA1 : A ≤ 1) (hℓ : 0 < ℓ) :
    Continuous (polarOuterRadial A ℓ tstar xstar) ∧
    (∀ q : E d × ℝ, A * √(tstar - q.2) ≤ ‖q.1 - xstar‖ - ℓ →
      (‖q.1 - xstar‖ - ℓ - A * √(tstar - q.2)) ^ (1 + A / 8) ≤
          polarOuterRadial A ℓ tstar xstar q ∧
        polarOuterRadial A ℓ tstar xstar q ≤
          (‖q.1 - xstar‖ - ℓ) * (‖q.1 - xstar‖ - ℓ + √(tstar - q.2)) ^ (A / 8)) ∧
    IsOpen (polarOuterDomain A ℓ tstar xstar) ∧
    ContDiffOn ℝ ∞ (polarOuterRadial A ℓ tstar xstar) (polarOuterDomain A ℓ tstar xstar) ∧
    ∀ q ∈ polarOuterDomain A ℓ tstar xstar,
      0 ≤ dₜ (polarOuterRadial A ℓ tstar xstar) q - lapₓ (polarOuterRadial A ℓ tstar xstar) q :=
  ⟨continuous_polarOuterRadial hA.le,
    fun _ hq ↦ ⟨rpow_one_add_le_polarOuter hA.le hq, polarOuter_le hA.le hq⟩,
    isOpen_polarOuterDomain, contDiffOn_polarOuterRadial hℓ, polarOuterRadial_heat hA hA1 hℓ⟩

/-- The inner polar barrier. Let `0 < A ≤ 1`, `ϑ = A/8`,
`ℓ = λ₁ > 0`, and `b₋(x, t) = B₋(y, s) = w Π^(-ϑ)`, `w = A ω - y`, `Π = w + ω`. Then

* `b₋` is continuous on the closed set `Γ₋ = {y ≤ A ω}`;
* on `Γ₋`: `0 ≤ b₋ ≤ w^(1-ϑ)` (and `b₋ = w Π^(-ϑ)` by definition, `polarInnerRadial_apply`);
* `b₋` is `C^∞` on the open set `G₋` and `∂ₜb₋ - Δb₋ ≤ 0` there. -/
theorem polar_barrier_inner (hA : 0 < A) (hA1 : A ≤ 1) (hℓ : 0 < ℓ) :
    ContinuousOn (polarInnerRadial A ℓ tstar xstar)
      {q | ‖q.1 - xstar‖ - ℓ ≤ A * √(tstar - q.2)} ∧
    (∀ q : E d × ℝ, ‖q.1 - xstar‖ - ℓ ≤ A * √(tstar - q.2) →
      0 ≤ polarInnerRadial A ℓ tstar xstar q ∧
        polarInnerRadial A ℓ tstar xstar q ≤
          (A * √(tstar - q.2) - (‖q.1 - xstar‖ - ℓ)) ^ (1 - A / 8)) ∧
    IsOpen (polarInnerDomain A ℓ tstar xstar) ∧
    ContDiffOn ℝ ∞ (polarInnerRadial A ℓ tstar xstar) (polarInnerDomain A ℓ tstar xstar) ∧
    ∀ q ∈ polarInnerDomain A ℓ tstar xstar,
      dₜ (polarInnerRadial A ℓ tstar xstar) q - lapₓ (polarInnerRadial A ℓ tstar xstar) q ≤ 0 :=
  ⟨continuousOn_polarInnerRadial (by linarith),
    fun _ hq ↦ ⟨polarInner_nonneg hq, polarInner_le hA.le (by linarith) hq⟩,
    isOpen_polarInnerDomain, contDiffOn_polarInnerRadial hℓ, polarInnerRadial_heat hA hA1 hℓ⟩

end Barriers

end BernoulliComparison
