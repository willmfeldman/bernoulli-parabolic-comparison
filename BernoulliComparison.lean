/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Setting
public import BernoulliComparison.Interface.Parabolic
public import BernoulliComparison.Statements.Main
public import BernoulliComparison.Corollary.StrictComparison
public import BernoulliComparison.Touching.Crossing
public import BernoulliComparison.Touching.Calculus
public import BernoulliComparison.Touching.Bridge
public import BernoulliComparison.Touching.Caloric
public import BernoulliComparison.Touching.PastPoints
public import BernoulliComparison.Touching.Extend
public import BernoulliComparison.Touching.ParOpen
public import BernoulliComparison.Touching.Classes
public import BernoulliComparison.Touching.ClassBridge
public import BernoulliComparison.Heat.Local
public import BernoulliComparison.Heat.Penalization
public import BernoulliComparison.Heat.Domain
public import BernoulliComparison.Heat.Comparison
public import BernoulliComparison.Heat.Dirichlet
public import BernoulliComparison.Crossing.Abstract
public import BernoulliComparison.Crossing.Config
public import BernoulliComparison.Crossing.Instance
public import BernoulliComparison.Barriers.Radial
public import BernoulliComparison.Barriers.Paraboloid
public import BernoulliComparison.Barriers.Slope
public import BernoulliComparison.Barriers.PolarBarrier
public import BernoulliComparison.Barriers.PolarRadial
public import BernoulliComparison.Convolution.Kernel
public import BernoulliComparison.Convolution.Basic
public import BernoulliComparison.Convolution.Preservation
public import BernoulliComparison.Convolution.Compose
public import BernoulliComparison.Barrier.Operators
public import BernoulliComparison.Barrier.Classical
public import BernoulliComparison.Barrier.Structural
public import BernoulliComparison.Barrier.ClosedDomain
public import BernoulliComparison.Barrier.Margin
public import BernoulliComparison.Main.DimZero
public import BernoulliComparison.Main.Core
public import BernoulliComparison.Main.Headline
public import BernoulliComparison.Contact.LocalConstants
public import BernoulliComparison.Contact.TouchConfig
public import BernoulliComparison.Contact.BumpPositivity
public import BernoulliComparison.Contact.Geometry
public import BernoulliComparison.Contact.FirstContact
public import BernoulliComparison.Contact.ZeroContact
public import BernoulliComparison.Contact.Structure
public import BernoulliComparison.Contact.Balls
public import BernoulliComparison.Contact.Data
public import BernoulliComparison.Polar.SouthReduction
public import BernoulliComparison.Polar.NorthInterior
public import BernoulliComparison.Polar.NorthExterior
public import BernoulliComparison.Polar.Sausage
public import BernoulliComparison.Polar.Unwind
public import BernoulliComparison.Polar.Exclusion
public import BernoulliComparison.NonPolar.Collinearity
public import BernoulliComparison.NonPolar.AxisRate
public import BernoulliComparison.NonPolar.SubRate
public import BernoulliComparison.NonPolar.Exclusion

/-!
# Comparison for the parabolic Bernoulli problem

This library proves the comparison principle for barrier-defined viscosity solutions of the
parabolic Bernoulli (one-phase) free boundary problem
`∂ₜu = Δu` in `{u > 0}`, `|∇u| = Q` on `∂{u > 0}`,
in a bounded open set `U ⊆ ℝᵈ` over the time interval `(0, T]`, with `Q` Lipschitz and bounded
below by a positive constant. The solution notions are defined in
`BernoulliComparison/Interface/Parabolic.lean`.

## Main results

* `BernoulliComparison.para_relaxed_comparison`: a relaxed subsolution `(u, E)` and a
  supersolution `v` that are strictly ordered on `E` near the parabolic boundary are strictly
  ordered on `E` in all of `Ū × [0, T]`.
* `BernoulliComparison.para_strict_comparison`: the same for a standard subsolution `u`, with
  `E` the closure of `{u > 0}`.

## Proof outline

A uniform margin at the parabolic boundary and a gap in `Q` (scaling `u` by `1 + δ` and `v` by
`1 - δ`) are followed by sup/inf-convolution; at a first contact point of the convolved pair, the
non-polar and polar cases of the touching-ball normals are each ruled out. The case `d = 0` is
handled separately.
-/

@[expose] public section
