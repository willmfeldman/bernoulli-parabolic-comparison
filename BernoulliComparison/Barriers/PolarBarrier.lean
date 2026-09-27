/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Self-similar polar barriers: the one-dimensional profiles

Let `0 < A ≤ 1`, `ϑ := A / 8`, and for `y ∈ ℝ`, `s ≥ 0` write `ω := √s`.

* **Outer profile** `B₊(y, s) = z Π^ϑ`, `z := y - A ω`, `Π := z + ω` (`polarOuter`), on
  `Γ₊ = {y ≥ A ω}`;
* **inner profile** `B₋(y, s) = w Π^(-ϑ)`, `w := A ω - y`, `Π := w + ω` (`polarInner`), on
  `Γ₋ = {y ≤ A ω}`.

Both are total functions on `ℝ × ℝ` (`Real.rpow`, `Real.sqrt`). Mathlib's `0 ^ (-ϑ) = 0`
(`Real.zero_rpow`) gives `B₋(0, 0) = 0` with no case split.

## Main statements

* (a) `continuous_polarOuter`, `polarOuter_nonneg`, `rpow_one_add_le_polarOuter`
  (`z^(1+ϑ) ≤ B₊`), `polarOuter_le` (`B₊ ≤ y (y + ω)^ϑ`);
* (b) `continuousOn_polarInner` (on `Γ₋`), `polarInner_nonneg`, `polarInner_le`
  (`B₋ ≤ w^(1-ϑ)`), `le_polarInner` (`w L^(-ϑ) ≤ B₋` when `Π ≤ L`);
* (c) smoothness `contDiffAt_polarOuter`, `contDiffAt_polarInner` (where `s ≠ 0`, `Π ≠ 0`); the
  partial derivatives `polarOuterDy`, `polarOuterDyy`, `polarOuterDs` (and `polarInner…`) with
  `hasDerivAt_…` lemmas; the differential inequalities `polarOuter_heat` (`-∂ₛB₊ - ∂²ᵧB₊ ≥
  (A/4) Π^ϑ/ω`), `polarOuterDy_nonneg`, `polarOuterDy_le` (`∂ᵧB₊ ≤ 2 Π^ϑ`), `polarInner_heat`
  (`-∂ₛB₋ - ∂²ᵧB₋ ≤ -(11A/64) Π^(-ϑ)/ω`), `polarInnerDy_nonpos`, `neg_le_polarInnerDy`.

The radial versions (in `x ∈ ℝᵈ`) are in `Barriers/PolarRadial.lean`; the barriers are used in
`Polar/NorthInterior.lean`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace BernoulliComparison

namespace Barriers

/-! ### A product rule for `f g^θ` -/

theorem hasDerivAt_mul_rpow {f g : ℝ → ℝ} {f' g' θ x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) (hg0 : g x ≠ 0) :
    HasDerivAt (fun r ↦ f r * g r ^ θ) (f' * g x ^ θ + f x * (θ * g x ^ (θ - 1) * g')) x := by
  convert hf.mul (hg.rpow_const (p := θ) (Or.inl hg0)) using 1
  ring

/-! ### Definitions -/

/-- The outer polar profile `B₊(y, s) = (y - A√s) (y - A√s + √s)^(A/8)`. -/
noncomputable def polarOuter (A y s : ℝ) : ℝ :=
  (y - A * √s) * (y - A * √s + √s) ^ (A / 8)

/-- The inner polar profile `B₋(y, s) = (A√s - y) (A√s - y + √s)^(-A/8)`. -/
noncomputable def polarInner (A y s : ℝ) : ℝ :=
  (A * √s - y) * (A * √s - y + √s) ^ (-(A / 8))

/-- `∂ᵧB₊ = Π^ϑ + ϑ z Π^(ϑ-1)`. -/
noncomputable def polarOuterDy (A y s : ℝ) : ℝ :=
  (y - A * √s + √s) ^ (A / 8) + A / 8 * (y - A * √s) * (y - A * √s + √s) ^ (A / 8 - 1)

/-- `∂²ᵧB₊ = 2ϑ Π^(ϑ-1) + ϑ(ϑ-1) z Π^(ϑ-2)`. -/
noncomputable def polarOuterDyy (A y s : ℝ) : ℝ :=
  2 * (A / 8) * (y - A * √s + √s) ^ (A / 8 - 1) +
    A / 8 * (A / 8 - 1) * (y - A * √s) * (y - A * √s + √s) ^ (A / 8 - 2)

/-- `∂ₛB₊ = (-A Π^ϑ + (1 - A) ϑ z Π^(ϑ-1)) / (2ω)`. -/
noncomputable def polarOuterDs (A y s : ℝ) : ℝ :=
  (-A * (y - A * √s + √s) ^ (A / 8) +
    (1 - A) * (A / 8) * (y - A * √s) * (y - A * √s + √s) ^ (A / 8 - 1)) / (2 * √s)

/-- `∂ᵧB₋ = -Π^(-ϑ) + ϑ w Π^(-ϑ-1)`. -/
noncomputable def polarInnerDy (A y s : ℝ) : ℝ :=
  -(A * √s - y + √s) ^ (-(A / 8)) +
    A / 8 * (A * √s - y) * (A * √s - y + √s) ^ (-(A / 8) - 1)

/-- `∂²ᵧB₋ = -2ϑ Π^(-ϑ-1) + ϑ(ϑ+1) w Π^(-ϑ-2)`. -/
noncomputable def polarInnerDyy (A y s : ℝ) : ℝ :=
  -(2 * (A / 8)) * (A * √s - y + √s) ^ (-(A / 8) - 1) +
    A / 8 * (A / 8 + 1) * (A * √s - y) * (A * √s - y + √s) ^ (-(A / 8) - 2)

/-- `∂ₛB₋ = (A Π^(-ϑ) - (1 + A) ϑ w Π^(-ϑ-1)) / (2ω)`. -/
noncomputable def polarInnerDs (A y s : ℝ) : ℝ :=
  (A * (A * √s - y + √s) ^ (-(A / 8)) -
    (1 + A) * (A / 8) * (A * √s - y) * (A * √s - y + √s) ^ (-(A / 8) - 1)) / (2 * √s)

variable {A y s : ℝ}

/-! ### (a) The outer profile: continuity and bounds -/

theorem continuous_polarOuter (hA : 0 ≤ A) :
    Continuous fun p : ℝ × ℝ ↦ polarOuter A p.1 p.2 := by
  unfold polarOuter
  have h1 : Continuous fun p : ℝ × ℝ ↦ p.1 - A * √p.2 :=
    continuous_fst.sub (continuous_const.mul continuous_snd.sqrt)
  exact h1.mul ((Real.continuous_rpow_const (by positivity)).comp (h1.add continuous_snd.sqrt))

theorem polarOuter_nonneg (hz : A * √s ≤ y) : 0 ≤ polarOuter A y s :=
  mul_nonneg (sub_nonneg.2 hz) (Real.rpow_nonneg (by positivity [sub_nonneg.2 hz]) _)

/-- Outer profile, lower bound: `z^(1+ϑ) ≤ B₊` on `Γ₊`. -/
theorem rpow_one_add_le_polarOuter (hA : 0 ≤ A) (hz : A * √s ≤ y) :
    (y - A * √s) ^ (1 + A / 8) ≤ polarOuter A y s := by
  have hz0 : 0 ≤ y - A * √s := sub_nonneg.2 hz
  rw [Real.rpow_add' hz0 (by positivity), Real.rpow_one, polarOuter]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hz0 (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (by positivity)) hz0

/-- Outer profile, upper bound: `B₊ ≤ y (y + ω)^ϑ` on `Γ₊`. -/
theorem polarOuter_le (hA : 0 ≤ A) (hz : A * √s ≤ y) :
    polarOuter A y s ≤ y * (y + √s) ^ (A / 8) := by
  have hz0 : 0 ≤ y - A * √s := sub_nonneg.2 hz
  have hAω : 0 ≤ A * √s := by positivity
  refine mul_le_mul (by linarith) (Real.rpow_le_rpow (by positivity) (by linarith)
    (by positivity)) (Real.rpow_nonneg (by positivity) _) (by linarith)

/-! ### (b) The inner profile: continuity and bounds -/

theorem polarInner_nonneg (hw : y ≤ A * √s) : 0 ≤ polarInner A y s :=
  mul_nonneg (sub_nonneg.2 hw) (Real.rpow_nonneg (by positivity [sub_nonneg.2 hw]) _)

/-- `B₋ ≤ Π^(1-ϑ)` on `Γ₋`. -/
theorem polarInner_le_rpow (hw : y ≤ A * √s) :
    polarInner A y s ≤ (A * √s - y + √s) ^ (1 - A / 8) := by
  have hw0 : 0 ≤ A * √s - y := sub_nonneg.2 hw
  rcases hw0.eq_or_lt with h0 | hpos
  · rw [polarInner, ← h0, zero_mul]
    exact Real.rpow_nonneg (by positivity) _
  · have hP : 0 < A * √s - y + √s := by positivity
    rw [show (1 : ℝ) - A / 8 = 1 + -(A / 8) by ring, Real.rpow_add hP, Real.rpow_one, polarInner]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hP.le _)

/-- Inner profile, upper bound: `B₋ ≤ w^(1-ϑ)` on `Γ₋`, for `0 ≤ A < 8`. -/
theorem polarInner_le (hA : 0 ≤ A) (hA8 : A < 8) (hw : y ≤ A * √s) :
    polarInner A y s ≤ (A * √s - y) ^ (1 - A / 8) := by
  have hw0 : 0 ≤ A * √s - y := sub_nonneg.2 hw
  rcases hw0.eq_or_lt with h0 | hpos
  · rw [polarInner, ← h0, zero_mul, Real.zero_rpow (by linarith)]
  · rw [show (1 : ℝ) - A / 8 = 1 + -(A / 8) by ring, Real.rpow_add hpos, Real.rpow_one,
      polarInner]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (by linarith)) hw0

/-- Lower bound for `B₋` in terms of an upper bound `L` for `Π`. -/
theorem le_polarInner (hA : 0 ≤ A) (hw : y ≤ A * √s) {L : ℝ} (hP : 0 < A * √s - y + √s)
    (hL : A * √s - y + √s ≤ L) : (A * √s - y) * L ^ (-(A / 8)) ≤ polarInner A y s :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hP hL (by linarith))
    (sub_nonneg.2 hw)

/-- Continuity of the inner profile: `B₋` is continuous on
`Γ₋ = {(y, s) : y ≤ A √s}` (for `A < 8`). At the vertex `Π = 0` this is the squeeze
`0 ≤ B₋ ≤ Π^(1-ϑ) → 0`. -/
theorem continuousOn_polarInner (hA8 : A < 8) :
    ContinuousOn (fun p : ℝ × ℝ ↦ polarInner A p.1 p.2) {p | p.1 ≤ A * √p.2} := by
  have hw : Continuous fun p : ℝ × ℝ ↦ A * √p.2 - p.1 :=
    (continuous_const.mul continuous_snd.sqrt).sub continuous_fst
  have hP : Continuous fun p : ℝ × ℝ ↦ A * √p.2 - p.1 + √p.2 := hw.add continuous_snd.sqrt
  intro p hp
  simp only [mem_setOf_eq] at hp
  rcases (show 0 ≤ A * √p.2 - p.1 + √p.2 by positivity [sub_nonneg.2 hp]).eq_or_lt with h0 | hpos
  · -- the vertex: squeeze
    have hw0 : A * √p.2 - p.1 = 0 := by
      have := Real.sqrt_nonneg p.2
      linarith [sub_nonneg.2 hp]
    have hval : polarInner A p.1 p.2 = 0 := by rw [polarInner, hw0, zero_mul]
    have hlim : Tendsto (fun q : ℝ × ℝ ↦ (A * √q.2 - q.1 + √q.2) ^ (1 - A / 8))
        (𝓝[{q | q.1 ≤ A * √q.2}] p) (𝓝 0) := by
      have := ((Real.continuous_rpow_const (q := 1 - A / 8) (by linarith)).comp hP).tendsto p
      simp only [Function.comp_def, ← h0, Real.zero_rpow (by linarith : (1 : ℝ) - A / 8 ≠ 0)]
        at this
      exact this.mono_left nhdsWithin_le_nhds
    rw [ContinuousWithinAt, hval]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq using polarInner_nonneg hq
    · filter_upwards [self_mem_nhdsWithin] with q hq using polarInner_le_rpow hq
  · refine ContinuousAt.continuousWithinAt ?_
    exact hw.continuousAt.mul (hP.continuousAt.rpow_const (Or.inl hpos.ne'))

/-! ### (c) Smoothness -/

theorem contDiffAt_polarOuter {n : WithTop ℕ∞} (hs : s ≠ 0) (hP : y - A * √s + √s ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ polarOuter A p.1 p.2) (y, s) := by
  have hω : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ √p.2) (y, s) :=
    (Real.contDiffAt_sqrt hs).comp (y, s) contDiffAt_snd
  have hz : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ p.1 - A * √p.2) (y, s) :=
    contDiffAt_fst.sub (contDiffAt_const.mul hω)
  exact hz.mul ((hz.add hω).rpow_const_of_ne hP)

theorem contDiffAt_polarInner {n : WithTop ℕ∞} (hs : s ≠ 0) (hP : A * √s - y + √s ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ polarInner A p.1 p.2) (y, s) := by
  have hω : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ √p.2) (y, s) :=
    (Real.contDiffAt_sqrt hs).comp (y, s) contDiffAt_snd
  have hw : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ A * √p.2 - p.1) (y, s) :=
    (contDiffAt_const.mul hω).sub contDiffAt_fst
  exact hw.mul ((hw.add hω).rpow_const_of_ne hP)

/-! ### (c) Partial derivatives -/

theorem hasDerivAt_polarOuter_y (hP : y - A * √s + √s ≠ 0) :
    HasDerivAt (fun y ↦ polarOuter A y s) (polarOuterDy A y s) y := by
  have hz : HasDerivAt (fun y ↦ y - A * √s) 1 y := (hasDerivAt_id y).sub_const _
  have := hasDerivAt_mul_rpow (θ := A / 8) hz (hz.add_const √s) hP
  convert this using 1
  simp only [polarOuterDy]
  ring

theorem hasDerivAt_polarOuterDy (hP : y - A * √s + √s ≠ 0) :
    HasDerivAt (fun y ↦ polarOuterDy A y s) (polarOuterDyy A y s) y := by
  have hz : HasDerivAt (fun y ↦ y - A * √s) 1 y := (hasDerivAt_id y).sub_const _
  have hPi : HasDerivAt (fun y ↦ y - A * √s + √s) 1 y := hz.add_const √s
  have h1 := hPi.rpow_const (p := A / 8) (Or.inl hP)
  have h2 := (hasDerivAt_mul_rpow (θ := A / 8 - 1) hz hPi hP).const_mul (A / 8)
  refine ((h1.add h2).congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  · simp only [polarOuterDyy, sub_sub, one_add_one_eq_two]
    ring
  · simp only [polarOuterDy, Pi.add_apply]
    ring

theorem hasDerivAt_polarOuter_s (hs : 0 < s) (hP : y - A * √s + √s ≠ 0) :
    HasDerivAt (fun s ↦ polarOuter A y s) (polarOuterDs A y s) s := by
  have hω : HasDerivAt (fun s ↦ √s) (1 / (2 * √s)) s := Real.hasDerivAt_sqrt hs.ne'
  have hz : HasDerivAt (fun s ↦ y - A * √s) (-(A * (1 / (2 * √s)))) s :=
    (hω.const_mul A).const_sub y
  have := hasDerivAt_mul_rpow (θ := A / 8) (g := fun s ↦ y - A * √s + √s) hz (hz.add hω) hP
  convert this using 1
  have hω0 : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  simp only [polarOuterDs]
  field_simp
  ring

theorem hasDerivAt_polarInner_y (hP : A * √s - y + √s ≠ 0) :
    HasDerivAt (fun y ↦ polarInner A y s) (polarInnerDy A y s) y := by
  have hw : HasDerivAt (fun y ↦ A * √s - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (A * √s)
  have := hasDerivAt_mul_rpow (θ := -(A / 8)) hw (hw.add_const √s) hP
  convert this using 1
  simp only [polarInnerDy]
  ring

theorem hasDerivAt_polarInnerDy (hP : A * √s - y + √s ≠ 0) :
    HasDerivAt (fun y ↦ polarInnerDy A y s) (polarInnerDyy A y s) y := by
  have hw : HasDerivAt (fun y ↦ A * √s - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (A * √s)
  have hPi : HasDerivAt (fun y ↦ A * √s - y + √s) (-1) y := hw.add_const √s
  have h1 := (hPi.rpow_const (p := -(A / 8)) (Or.inl hP)).neg
  have h2 := (hasDerivAt_mul_rpow (θ := -(A / 8) - 1) hw hPi hP).const_mul (A / 8)
  refine ((h1.add h2).congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  · simp only [polarInnerDyy, sub_sub, one_add_one_eq_two]
    ring
  · simp only [polarInnerDy, Pi.add_apply, Pi.neg_apply]
    ring

theorem hasDerivAt_polarInner_s (hs : 0 < s) (hP : A * √s - y + √s ≠ 0) :
    HasDerivAt (fun s ↦ polarInner A y s) (polarInnerDs A y s) s := by
  have hω : HasDerivAt (fun s ↦ √s) (1 / (2 * √s)) s := Real.hasDerivAt_sqrt hs.ne'
  have hw : HasDerivAt (fun s ↦ A * √s - y) (A * (1 / (2 * √s))) s :=
    (hω.const_mul A).sub_const y
  have := hasDerivAt_mul_rpow (θ := -(A / 8)) (g := fun s ↦ A * √s - y + √s) hw (hw.add hω)
    hP
  convert this using 1
  have hω0 : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  simp only [polarInnerDs]
  field_simp
  ring

/-! ### (c) The differential inequalities -/

/-- Heat inequality for the outer profile: on `{s > 0, z ≥ 0}`, for `0 < A ≤ 1`:
`-∂ₛB₊ - ∂²ᵧB₊ ≥ (A/4) Π^ϑ / ω`. After multiplying by `2ωΠ^(2-ϑ)` this is the polynomial
inequality `AΠ² - (1-A)ϑzΠ - 4ϑωΠ + 2ϑ(1-ϑ)ωz ≥ (A/2)Π²` with `z = Π - ω`. -/
theorem polarOuter_heat (hA : 0 < A) (hA1 : A ≤ 1) (hs : 0 < s) (hz : A * √s ≤ y) :
    A / 4 * (y - A * √s + √s) ^ (A / 8) / √s ≤ -polarOuterDs A y s - polarOuterDyy A y s := by
  unfold polarOuterDs polarOuterDyy
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  set q := √s
  have hz0 : 0 ≤ y - A * q := sub_nonneg.2 hz
  set z := y - A * q
  have hP : 0 < z + q := by positivity
  rw [Real.rpow_sub_one hP.ne', Real.rpow_sub hP, Real.rpow_two]
  have hX : 0 < (z + q) ^ (A / 8) := Real.rpow_pos_of_pos hP _
  set X := (z + q) ^ (A / 8)
  set P := z + q with hPdef
  set poly := A * P ^ 2 - (1 - A) * (A / 8) * z * P - 4 * (A / 8) * q * P +
    2 * (A / 8) * (1 - A / 8) * q * z - A / 2 * P ^ 2 with hpoly
  have key : -((-A * X + (1 - A) * (A / 8) * z * (X / P)) / (2 * q)) -
      (2 * (A / 8) * (X / P) + A / 8 * (A / 8 - 1) * z * (X / P ^ 2)) - A / 4 * X / q =
      X / (2 * q * P ^ 2) * poly := by
    rw [hpoly]; field_simp; ring
  have hpoly0 : 0 ≤ poly := by
    have h1 : 0 ≤ (A / 8) * (1 + A + 2 * (A / 8)) * (P * z) := by positivity
    have h2 : 0 ≤ 2 * (A / 8) * (1 - A / 8) * (z * (z + 2 * q)) := by
      have : 0 ≤ 1 - A / 8 := by linarith
      positivity
    rw [hpoly, hPdef]
    rw [hPdef] at h1
    nlinarith
  have : 0 ≤ X / (2 * q * P ^ 2) * poly := mul_nonneg (by positivity) hpoly0
  linarith

/-- The outer profile is nondecreasing in `y`: `0 ≤ ∂ᵧB₊` on `{s > 0, z ≥ 0}`. -/
theorem polarOuterDy_nonneg (hA : 0 ≤ A) (hs : 0 < s) (hz : A * √s ≤ y) :
    0 ≤ polarOuterDy A y s := by
  unfold polarOuterDy
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  have hz0 : 0 ≤ y - A * √s := sub_nonneg.2 hz
  have hP : 0 < y - A * √s + √s := by positivity
  have := Real.rpow_nonneg hP.le (A / 8)
  have := Real.rpow_nonneg hP.le (A / 8 - 1)
  positivity

/-- Gradient bound for the outer profile: `∂ᵧB₊ ≤ 2 Π^ϑ` on `{s > 0, z ≥ 0}`, `A ≤ 8`. -/
theorem polarOuterDy_le (hA8 : A ≤ 8) (hs : 0 < s) (hz : A * √s ≤ y) :
    polarOuterDy A y s ≤ 2 * (y - A * √s + √s) ^ (A / 8) := by
  unfold polarOuterDy
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  set q := √s
  have hz0 : 0 ≤ y - A * q := sub_nonneg.2 hz
  set z := y - A * q
  have hP : 0 < z + q := by positivity
  rw [Real.rpow_sub_one hP.ne']
  have hX : 0 < (z + q) ^ (A / 8) := Real.rpow_pos_of_pos hP _
  set X := (z + q) ^ (A / 8)
  have : A / 8 * z * (X / (z + q)) ≤ X := by
    rw [mul_div_assoc', div_le_iff₀ hP]
    have : A / 8 * z ≤ z + q := by nlinarith
    nlinarith
  linarith

/-- Heat inequality for the inner profile: on `{s > 0, w ≥ 0}`, for `0 < A ≤ 1`:
`-∂ₛB₋ - ∂²ᵧB₋ ≤ -(11A/64) Π^(-ϑ) / ω`. After multiplying by `2ωΠ^(2+ϑ)` this is the
polynomial inequality `-AΠ² + (1+A)ϑwΠ + 4ϑωΠ - 2ϑ(1+ϑ)ωw ≤ -(11A/32)Π²` with `w = Π - ω`. -/
theorem polarInner_heat (hA : 0 < A) (hA1 : A ≤ 1) (hs : 0 < s) (hw : y ≤ A * √s) :
    -polarInnerDs A y s - polarInnerDyy A y s ≤
      -(11 * A / 64 * (A * √s - y + √s) ^ (-(A / 8)) / √s) := by
  unfold polarInnerDs polarInnerDyy
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  set q := √s
  have hw0 : 0 ≤ A * q - y := sub_nonneg.2 hw
  set w := A * q - y
  have hP : 0 < w + q := by positivity
  rw [Real.rpow_sub_one hP.ne', Real.rpow_sub hP, Real.rpow_two]
  have hX : 0 < (w + q) ^ (-(A / 8)) := Real.rpow_pos_of_pos hP _
  set X := (w + q) ^ (-(A / 8))
  set P := w + q with hPdef
  set poly := -(A * P ^ 2) + (1 + A) * (A / 8) * w * P + 4 * (A / 8) * q * P -
    2 * (A / 8) * (A / 8 + 1) * q * w + 11 * A / 32 * P ^ 2 with hpoly
  have key : -((A * X - (1 + A) * (A / 8) * w * (X / P)) / (2 * q)) -
      (-(2 * (A / 8)) * (X / P) + A / 8 * (A / 8 + 1) * w * (X / P ^ 2)) +
      11 * A / 64 * X / q = X / (2 * q * P ^ 2) * poly := by
    rw [hpoly]; field_simp; ring
  have hpoly0 : poly ≤ 0 := by
    have h1 : 0 ≤ (A / 8) * (A + 2 * (A / 8)) * (q * P) := by positivity
    have h2 : 0 ≤ (A / 8) * (P * w) := by positivity
    have h3 : 0 ≤ 2 * (A / 8) * (1 + A / 8) * (w * (w + 2 * q)) := by positivity
    have h4 : 0 ≤ A * (1 - A) * P ^ 2 := by
      have : 0 ≤ 1 - A := by linarith
      positivity
    rw [hpoly, hPdef]
    rw [hPdef] at h1 h2 h4
    nlinarith
  have : X / (2 * q * P ^ 2) * poly ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hpoly0
  linarith

/-- The inner profile is nonincreasing in `y`: `∂ᵧB₋ ≤ 0` on `{s > 0, w ≥ 0}`, `A ≤ 8`. -/
theorem polarInnerDy_nonpos (hA8 : A ≤ 8) (hs : 0 < s) (hw : y ≤ A * √s) :
    polarInnerDy A y s ≤ 0 := by
  unfold polarInnerDy
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  set q := √s
  have hw0 : 0 ≤ A * q - y := sub_nonneg.2 hw
  set w := A * q - y
  have hP : 0 < w + q := by positivity
  rw [Real.rpow_sub_one hP.ne']
  have hX : 0 < (w + q) ^ (-(A / 8)) := Real.rpow_pos_of_pos hP _
  set X := (w + q) ^ (-(A / 8))
  have : A / 8 * w * (X / (w + q)) ≤ X := by
    rw [mul_div_assoc', div_le_iff₀ hP]
    have : A / 8 * w ≤ w + q := by nlinarith
    nlinarith
  linarith

/-- Gradient bound for the inner profile: `-Π^(-ϑ) ≤ ∂ᵧB₋` on `{s > 0, w ≥ 0}`. -/
theorem neg_le_polarInnerDy (hA : 0 ≤ A) (hs : 0 < s) (hw : y ≤ A * √s) :
    -(A * √s - y + √s) ^ (-(A / 8)) ≤ polarInnerDy A y s := by
  unfold polarInnerDy
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  have hw0 : 0 ≤ A * √s - y := sub_nonneg.2 hw
  have hP : 0 < A * √s - y + √s := by positivity
  have := Real.rpow_nonneg hP.le (-(A / 8) - 1)
  have : 0 ≤ A / 8 * (A * √s - y) * (A * √s - y + √s) ^ (-(A / 8) - 1) := by positivity
  linarith

end Barriers

end BernoulliComparison
