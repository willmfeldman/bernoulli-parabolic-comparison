import Mathlib

/-!
# Challenge vocabulary: the ambient space, space-time operators, strict ordering on a set

Part of the trusted statement surface; imports `Mathlib` only. Restates, token for token, the
definitions of the library file `BernoulliComparison/Interface/Setting.lean`.

* `E d` is `EuclideanSpace ℝ (Fin d)`. Space-time points are `p : E d × ℝ`, with `p.1` the space
  and `p.2` the time variable. Note that Mathlib puts the *sup* norm on the product `E d × ℝ`.
* `gradₓ`, `lapₓ`, `dₜ` are Mathlib's `gradient` (`∇`), Laplacian (`Δ`) and `deriv`, applied to
  the time slice `y ↦ φ (y, t)` (resp. the space slice `s ↦ φ (x, s)`) through `p`.
* `PrecOn u v S F` says `u < v` at every point of `S ∩ F`.
-/

open Set Filter Topology
open scoped Gradient Laplacian

namespace BernoulliComparison

/-- The ambient Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- Spatial gradient `∇ₓφ(x, t)`: the gradient of `y ↦ φ (y, t)` at `x`. -/
noncomputable def gradₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : E d :=
  ∇ (fun y ↦ φ (y, p.2)) p.1

/-- Spatial Laplacian `Δₓφ(x, t)`: the Laplacian of `y ↦ φ (y, t)` at `x`. -/
noncomputable def lapₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  Δ (fun y ↦ φ (y, p.2)) p.1

/-- Time derivative `∂ₜφ(x, t)`: the (two-sided) derivative of `s ↦ φ (x, s)` at `t`. -/
noncomputable def dₜ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  deriv (fun s ↦ φ (p.1, s)) p.2

section PrecOn

variable {X : Type*}

/-- Strict ordering on a set: `u < v` at every point of `Eset ∩ F`. -/
def PrecOn (u v : X → ℝ) (Eset F : Set X) : Prop := ∀ p ∈ Eset ∩ F, u p < v p

end PrecOn

end BernoulliComparison
