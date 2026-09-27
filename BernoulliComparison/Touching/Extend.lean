/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.Caloric
public import BernoulliComparison.Heat.Local

/-!
# Local test functions: germ-locality and global extension

The operators `dₜ`, `gradₓ`, `lapₓ` depend only on germs, touching is local, and a test function
defined near a point can be extended to a globally `C^∞` function.

## Main definitions

* `IsTestFunAt φ p`: `φ` is `C^∞` on some open set containing `p`.

## Main statements

The bump extension `exists_contDiff_eventuallyEq` and the germ-locality lemmas
(`dₜ_congr_of_eventuallyEq`, `lapₓ_congr_of_eventuallyEq`, `gradₓ_congr_of_eventuallyEq`,
`CrossesFromAbove.congr_of_eventuallyEq`, `CrossesFromBelow.congr_of_eventuallyEq`) are in
`Heat/Local.lean`. Here:

* `crossesFromAbove_congr_of_eventuallyEq`, `crossesFromBelow_congr_of_eventuallyEq`: `iff` forms;
* `IsTestFunAt.exists_contDiff_eventuallyEq`, `exists_contDiff_eqOn_ball` (global
  extension, pointwise and on a ball);
* `forall_isTestFunAt_crossesFromAbove_iff`, `forall_isTestFunAt_crossesFromBelow_iff`: testing
  a germ-invariant property with local test functions is the same as testing it with globally
  `C^∞` functions.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Locality of touching -/

section Locality

variable {S : Set (E d × ℝ)} {u φ ψ : E d × ℝ → ℝ} {p : E d × ℝ}

theorem crossesFromAbove_congr_of_eventuallyEq (hφψ : φ =ᶠ[𝓝 p] ψ) :
    CrossesFromAbove S u φ p ↔ CrossesFromAbove S u ψ p :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hφψ, fun h ↦ h.congr_of_eventuallyEq hφψ.symm⟩

theorem crossesFromBelow_congr_of_eventuallyEq (hφψ : φ =ᶠ[𝓝 p] ψ) :
    CrossesFromBelow S u φ p ↔ CrossesFromBelow S u ψ p :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hφψ, fun h ↦ h.congr_of_eventuallyEq hφψ.symm⟩

end Locality

/-! ### Test functions and global extension -/

/-- `φ` is a *test function at `p`*: `φ` is `C^∞` on some open set
containing `p`. Values of `φ` away from that set are irrelevant. -/
def IsTestFunAt (φ : E d × ℝ → ℝ) (p : E d × ℝ) : Prop :=
  ∃ W : Set (E d × ℝ), IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ φ W

section TestFun

variable {φ ψ : E d × ℝ → ℝ} {p : E d × ℝ}

/-- A globally `C^∞` function is a test function at every point. -/
theorem _root_.ContDiff.isTestFunAt (hφ : ContDiff ℝ ∞ φ) (p : E d × ℝ) : IsTestFunAt φ p :=
  ⟨univ, isOpen_univ, mem_univ p, hφ.contDiffOn⟩

theorem IsTestFunAt.congr_of_eventuallyEq (hφ : IsTestFunAt φ p) (hφψ : φ =ᶠ[𝓝 p] ψ) :
    IsTestFunAt ψ p := by
  obtain ⟨W, hW, hpW, hφW⟩ := hφ
  obtain ⟨N, hN, hNo, hpN⟩ := _root_.mem_nhds_iff.1 hφψ
  refine ⟨W ∩ N, hW.inter hNo, ⟨hpW, hpN⟩, ?_⟩
  exact (hφW.mono inter_subset_left).congr fun q hq ↦ (hN hq.2).symm

/-- A test function at `p` agrees near `p` with a globally `C^∞` function. -/
theorem IsTestFunAt.exists_contDiff_eventuallyEq (hφ : IsTestFunAt φ p) :
    ∃ ψ : E d × ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ ψ =ᶠ[𝓝 p] φ := by
  obtain ⟨W, hW, hpW, hφW⟩ := hφ
  exact BernoulliComparison.exists_contDiff_eventuallyEq hW hpW hφW

/-- Global extension of a local test function. If `φ` is `C^∞` on an open `W ∋ p`, there are a
globally `C^∞` `ψ` and `r > 0` with `ψ = φ` on the (sup-metric) ball `ball p r`. This ball
contains the Euclidean space-time ball of radius `r` about `p`, so the statement is at least as
strong as its Euclidean form. -/
theorem exists_contDiff_eqOn_ball {W : Set (E d × ℝ)} (hW : IsOpen W) (hpW : p ∈ W)
    (hφ : ContDiffOn ℝ ∞ φ W) :
    ∃ ψ : E d × ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ ∃ r > 0, EqOn ψ φ (ball p r) := by
  obtain ⟨ψ, hψ, hψφ⟩ := exists_contDiff_eventuallyEq hW hpW hφ
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 hψφ
  exact ⟨ψ, hψ, r, hr, fun q hq ↦ hsub hq⟩

end TestFun

/-! ### Local versus global tests -/

section LocalGlobal

variable {S : Set (E d × ℝ)} {u : E d × ℝ → ℝ} {p : E d × ℝ}

/-- For a property `P` of test functions that depends only on the germ at `p`, testing touching
from above with local test functions is equivalent to testing with globally `C^∞` functions. -/
theorem forall_isTestFunAt_crossesFromAbove_iff {P : (E d × ℝ → ℝ) → Prop}
    (hP : ∀ φ ψ, φ =ᶠ[𝓝 p] ψ → P φ → P ψ) :
    (∀ φ, IsTestFunAt φ p → CrossesFromAbove S u φ p → P φ) ↔
      ∀ φ, ContDiff ℝ ∞ φ → CrossesFromAbove S u φ p → P φ := by
  refine ⟨fun h φ hφ hc ↦ h φ (hφ.isTestFunAt p) hc, fun h φ hφ hc ↦ ?_⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hφ.exists_contDiff_eventuallyEq
  exact hP ψ φ hψφ (h ψ hψ (hc.congr_of_eventuallyEq hψφ.symm))

/-- For a property `P` of test functions that depends only on the germ at `p`, testing touching
from below with local test functions is equivalent to testing with globally `C^∞` functions. -/
theorem forall_isTestFunAt_crossesFromBelow_iff {P : (E d × ℝ → ℝ) → Prop}
    (hP : ∀ φ ψ, φ =ᶠ[𝓝 p] ψ → P φ → P ψ) :
    (∀ φ, IsTestFunAt φ p → CrossesFromBelow S u φ p → P φ) ↔
      ∀ φ, ContDiff ℝ ∞ φ → CrossesFromBelow S u φ p → P φ := by
  refine ⟨fun h φ hφ hc ↦ h φ (hφ.isTestFunAt p) hc, fun h φ hφ hc ↦ ?_⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hφ.exists_contDiff_eventuallyEq
  exact hP ψ φ hψφ (h ψ hψ (hc.congr_of_eventuallyEq hψφ.symm))

end LocalGlobal

end BernoulliComparison
