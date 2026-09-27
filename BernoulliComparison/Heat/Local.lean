/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.Crossing
public import BernoulliComparison.Touching.Calculus
public import BernoulliComparison.Touching.Bridge
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Localization of test functions

The touching classes `IsCaloricSub` / `IsCaloricSuper` (`Touching/Crossing.lean`) quantify over
globally `C^∞` test functions. Crossing is a local property, so one may test with functions which
are smooth only near the contact point. This file makes that observation formal:

* `exists_contDiff_eventuallyEq`: a function `C^∞` on an open set `N ∋ p` agrees near `p` with a
  globally `C^∞` function (multiply by a smooth bump);
* `dₜ_congr_of_eventuallyEq`, `lapₓ_congr_of_eventuallyEq`, `gradₓ_congr_of_eventuallyEq`: the
  space-time operators only depend on the germ at `p`;
* `CrossesFromAbove.congr_of_eventuallyEq` (and `Below`): crossing only depends on the germ;
* `IsCaloricSub.heat_nonpos_of_contDiffOn`, `IsCaloricSuper.heat_nonneg_of_contDiffOn`: the
  touching inequality for locally smooth test functions;
* `dₜ_sub_lapₓ_add_mul_add_of_contDiffOn`: the heat operator of `ψ + (a h + c)` for locally
  smooth `ψ`, `h`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Laplacian

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Smooth extension from a neighbourhood -/

/-- A function which is `C^∞` on an open set `N ∋ p` agrees near `p` with a globally `C^∞`
function (namely, its product with a smooth bump supported in `N`). -/
theorem exists_contDiff_eventuallyEq {ψ : E d × ℝ → ℝ} {N : Set (E d × ℝ)} (hN : IsOpen N)
    {p : E d × ℝ} (hp : p ∈ N) (hψ : ContDiffOn ℝ ∞ ψ N) :
    ∃ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ ∧ φ =ᶠ[𝓝 p] ψ := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hN p hp
  let χ : ContDiffBump p := ⟨R / 4, R / 2, by positivity, by linarith⟩
  refine ⟨fun q ↦ χ q * ψ q, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun q ↦ ?_
    by_cases hq : q ∈ N
    · exact χ.contDiff.contDiffAt.mul (hψ.contDiffAt (hN.mem_nhds hq))
    · have hqs : q ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        intro hq'
        exact hq (hball (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hq') (by
          change R / 2 < R; linarith))))
      have h0 : (fun q ↦ χ q * ψ q) =ᶠ[𝓝 q] fun _ ↦ 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hqs)] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  · filter_upwards [χ.eventuallyEq_one] with q hq
    simp [hq]

/-! ### Locality of the space-time operators -/

section Congr

variable {φ ψ : E d × ℝ → ℝ} {p : E d × ℝ}

theorem eventuallyEq_sliceT (h : φ =ᶠ[𝓝 p] ψ) :
    (fun s : ℝ ↦ φ (p.1, s)) =ᶠ[𝓝 p.2] fun s ↦ ψ (p.1, s) := by
  have ht : Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝 p.2) (𝓝 p) := by
    simpa using ((continuous_const.prodMk continuous_id).tendsto p.2 :
      Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝 p.2) (𝓝 (p.1, p.2)))
  exact h.comp_tendsto ht

theorem eventuallyEq_sliceX (h : φ =ᶠ[𝓝 p] ψ) :
    (fun y : E d ↦ φ (y, p.2)) =ᶠ[𝓝 p.1] fun y ↦ ψ (y, p.2) := by
  have ht : Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 p) := by
    simpa using ((continuous_id.prodMk continuous_const).tendsto p.1 :
      Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 (p.1, p.2)))
  exact h.comp_tendsto ht

theorem dₜ_congr_of_eventuallyEq (h : φ =ᶠ[𝓝 p] ψ) : dₜ φ p = dₜ ψ p :=
  (eventuallyEq_sliceT h).deriv_eq

theorem lapₓ_congr_of_eventuallyEq (h : φ =ᶠ[𝓝 p] ψ) : lapₓ φ p = lapₓ ψ p :=
  (InnerProductSpace.laplacian_congr_nhds (eventuallyEq_sliceX h)).eq_of_nhds

theorem gradₓ_congr_of_eventuallyEq (h : φ =ᶠ[𝓝 p] ψ) : gradₓ φ p = gradₓ ψ p := by
  simp only [gradₓ, gradient, (eventuallyEq_sliceX h).fderiv_eq]

/-- `∀ᶠ q in 𝓝 p, P q` gives a backward cylinder at `p` on which `P` holds. -/
theorem exists_parCyl_of_eventually {P : E d × ℝ → Prop} (h : ∀ᶠ q in 𝓝 p, P q) :
    ∃ ρ > 0, ∀ q ∈ parCyl p.1 p.2 ρ, P q := by
  obtain ⟨ρ, hρ, hsub⟩ :=
    (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0)
      (eventually_forall_closedParCyl h)).exists
  exact ⟨ρ, hρ, fun q hq ↦ hsub q (mem_closedParCyl.2 (by
    obtain ⟨h1, h2, h3⟩ := mem_parCyl.1 hq
    exact ⟨h1.le, h2.le, h3⟩))⟩

variable {S : Set (E d × ℝ)} {u : E d × ℝ → ℝ}

theorem CrossesFromAbove.congr_of_eventuallyEq (hc : CrossesFromAbove S u φ p)
    (h : φ =ᶠ[𝓝 p] ψ) : CrossesFromAbove S u ψ p := by
  obtain ⟨ρ, hρ, hq⟩ := exists_parCyl_of_eventually h
  exact hc.congr hρ fun q hqS ↦ hq q hqS.2

theorem CrossesFromBelow.congr_of_eventuallyEq (hc : CrossesFromBelow S u φ p)
    (h : φ =ᶠ[𝓝 p] ψ) : CrossesFromBelow S u ψ p := by
  obtain ⟨ρ, hρ, hq⟩ := exists_parCyl_of_eventually h
  exact hc.congr hρ fun q hqS ↦ hq q hqS.2

end Congr

/-! ### Testing with locally smooth functions -/

section Test

variable {S N : Set (E d × ℝ)} {u ψ : E d × ℝ → ℝ} {p : E d × ℝ}

/-- **Localization.** A subcaloric function satisfies the touching inequality for test
functions which are only `C^∞` on an open neighbourhood `N` of the contact point. -/
theorem IsCaloricSub.heat_nonpos_of_contDiffOn (hu : IsCaloricSub S u) (hN : IsOpen N)
    (hpN : p ∈ N) (hψ : ContDiffOn ℝ ∞ ψ N) (hc : CrossesFromAbove S u ψ p) :
    dₜ ψ p - lapₓ ψ p ≤ 0 := by
  obtain ⟨φ, hφ, hφψ⟩ := exists_contDiff_eventuallyEq hN hpN hψ
  have := hu φ hφ p (hc.congr_of_eventuallyEq hφψ.symm)
  rwa [dₜ_congr_of_eventuallyEq hφψ, lapₓ_congr_of_eventuallyEq hφψ] at this

/-- **Localization** (supercaloric version). A supercaloric function satisfies the touching
inequality for test functions which are only `C^∞` on an open neighbourhood `N` of the contact
point. -/
theorem IsCaloricSuper.heat_nonneg_of_contDiffOn (hu : IsCaloricSuper S u) (hN : IsOpen N)
    (hpN : p ∈ N) (hψ : ContDiffOn ℝ ∞ ψ N) (hc : CrossesFromBelow S u ψ p) :
    0 ≤ dₜ ψ p - lapₓ ψ p := by
  obtain ⟨φ, hφ, hφψ⟩ := exists_contDiff_eventuallyEq hN hpN hψ
  have := hu φ hφ p (hc.congr_of_eventuallyEq hφψ.symm)
  rwa [dₜ_congr_of_eventuallyEq hφψ, lapₓ_congr_of_eventuallyEq hφψ] at this

/-- Heat operator of a perturbation `ψ + (a h + c)` of functions which are `C^∞` near `p`. -/
theorem dₜ_sub_lapₓ_add_mul_add_of_contDiffOn {h : E d × ℝ → ℝ} (hN : IsOpen N) (hpN : p ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ N) (hh : ContDiffOn ℝ ∞ h N) (a c : ℝ) :
    dₜ (fun q ↦ ψ q + (a * h q + c)) p - lapₓ (fun q ↦ ψ q + (a * h q + c)) p =
      (dₜ ψ p - lapₓ ψ p) + a * (dₜ h p - lapₓ h p) := by
  obtain ⟨φ, hφ, hφψ⟩ := exists_contDiff_eventuallyEq hN hpN hψ
  obtain ⟨k, hk, hkh⟩ := exists_contDiff_eventuallyEq hN hpN hh
  have hsum : (fun q ↦ φ q + (a * k q + c)) =ᶠ[𝓝 p] fun q ↦ ψ q + (a * h q + c) := by
    filter_upwards [hφψ, hkh] with q h1 h2
    rw [h1, h2]
  rw [← dₜ_congr_of_eventuallyEq hsum, ← lapₓ_congr_of_eventuallyEq hsum,
    dₜ_sub_lapₓ_add_mul_add (hφ.of_le (by norm_cast)) (hk.of_le (by norm_cast)),
    dₜ_congr_of_eventuallyEq hφψ, lapₓ_congr_of_eventuallyEq hφψ,
    dₜ_congr_of_eventuallyEq hkh, lapₓ_congr_of_eventuallyEq hkh]

end Test

end BernoulliComparison
