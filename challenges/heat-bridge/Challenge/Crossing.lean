import Challenge.Parabolic

/-!
# Challenge vocabulary: viscosity sub- and supersolutions of the heat equation

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Parabolic`).
Restates, token for token, definitions of the library file
`BernoulliComparison/Touching/Crossing.lean`.

This is the standard notion of viscosity solution of the heat equation `∂ₜu = Δu` for parabolic
problems (Crandall–Ishii–Lions, §8), with test functions touching on backward parabolic
cylinders:

* `parCyl x t r = B_r(x) × (t - r², t]` is the backward parabolic cylinder (Euclidean ball in
  `ℝᵈ`); only the past of the touching point is used.
* `φ` crosses `u` from above in `S` at `p` if `p ∈ S`, `u p = φ p`, and `u ≤ φ` on
  `S ∩ parCyl p r` for some `r > 0` (from below: `φ ≤ u` there).
* `IsCaloricSub O u`: for every globally `C^∞` test function `φ` crossing `u` from above in `O`
  at `p`, `∂ₜφ(p) - Δₓφ(p) ≤ 0`. `IsCaloricSuper O u`: for every `C^∞` `φ` crossing `u` from
  below in `O` at `p`, `∂ₜφ(p) - Δₓφ(p) ≥ 0`.

No continuity is built into `IsCaloricSub`/`IsCaloricSuper`; in the challenge, the continuity of
`u` on `U × I` is part of the hypothesis.
-/

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-- The backward parabolic cylinder `B_r(x) × (t - r², t]`. -/
def parCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := ball x r ×ˢ Ioc (t - r ^ 2) t

/-- `φ` crosses (touches) `u` from above in `S` at `p`: `p ∈ S`, `u p = φ p`, and `u ≤ φ` on
`S ∩ parCyl p.1 p.2 r` for some `r > 0`. -/
def CrossesFromAbove (S : Set (E d × ℝ)) (u φ : E d × ℝ → ℝ) (p : E d × ℝ) : Prop :=
  p ∈ S ∧ u p = φ p ∧ ∃ r > 0, ∀ q ∈ S ∩ parCyl p.1 p.2 r, u q ≤ φ q

/-- `φ` crosses (touches) `u` from below in `S` at `p`: `p ∈ S`, `u p = φ p`, and `φ ≤ u` on
`S ∩ parCyl p.1 p.2 r` for some `r > 0`. -/
def CrossesFromBelow (S : Set (E d × ℝ)) (u φ : E d × ℝ → ℝ) (p : E d × ℝ) : Prop :=
  p ∈ S ∧ u p = φ p ∧ ∃ r > 0, ∀ q ∈ S ∩ parCyl p.1 p.2 r, φ q ≤ u q

/-- Viscosity subsolution of the heat equation in `O`: whenever a `C^∞` function `φ` crosses `u`
from above in `O` at `p`, `∂ₜφ(p) - Δₓφ(p) ≤ 0`. -/
def IsCaloricSub (O : Set (E d × ℝ)) (u : E d × ℝ → ℝ) : Prop :=
  ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ p, CrossesFromAbove O u φ p → dₜ φ p - lapₓ φ p ≤ 0

/-- Viscosity supersolution of the heat equation in `O`: whenever a `C^∞` function `φ` crosses
`u` from below in `O` at `p`, `∂ₜφ(p) - Δₓφ(p) ≥ 0`. -/
def IsCaloricSuper (O : Set (E d × ℝ)) (u : E d × ℝ → ℝ) : Prop :=
  ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ p, CrossesFromBelow O u φ p → 0 ≤ dₜ φ p - lapₓ φ p

end BernoulliComparison
