/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.LinearAlgebra.Trace

/-!
# Ambient space, space-time differential operators, strict ordering on a set

This file fixes the basic setting in which the solution notions of
`BernoulliComparison/Interface/Parabolic.lean` are stated.

## Main definitions

* `BernoulliComparison.E d`: the Euclidean space `ℝᵈ`.
* `BernoulliComparison.gradₓ`, `BernoulliComparison.lapₓ`, `BernoulliComparison.dₜ`: spatial
  gradient, spatial Laplacian and time derivative of a space-time function.
* `BernoulliComparison.PrecOn`: the strict ordering `u < v` on the intersection of two sets.

## Conventions

* All functions are total (`E d → ℝ`, `E d × ℝ → ℝ`); every predicate restricts to its domain
  explicitly, and values outside the domain are never used.
* Space-time points are `p : E d × ℝ`, with `p.1` the space and `p.2` the time variable.
* `E d × ℝ` carries the product (sup) metric.
-/

@[expose] public section

open Set Filter Topology
open scoped Gradient Laplacian

namespace BernoulliComparison

/-- The ambient Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-! ### Differential operators -/

/-- Spatial gradient `∇ₓφ(x,t)` of a space-time function (gradient of the time slice). -/
noncomputable def gradₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : E d :=
  ∇ (fun y ↦ φ (y, p.2)) p.1

/-- Spatial Laplacian `Δₓφ(x,t)` of a space-time function (Laplacian of the time slice). -/
noncomputable def lapₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  Δ (fun y ↦ φ (y, p.2)) p.1

/-- Time derivative `∂ₜφ(x,t)` of a space-time function. -/
noncomputable def dₜ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  deriv (fun s ↦ φ (p.1, s)) p.2

/-! ### Strict ordering on a set -/

section PrecOn

variable {X : Type*}

/-- The strict ordering `u ≺_E v` on `F`: `u < v` at every point of `E ∩ F`. -/
def PrecOn (u v : X → ℝ) (Eset F : Set X) : Prop := ∀ p ∈ Eset ∩ F, u p < v p

end PrecOn

end BernoulliComparison
