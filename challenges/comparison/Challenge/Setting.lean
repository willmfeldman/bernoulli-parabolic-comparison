import Mathlib

/-!
# Challenge vocabulary: the ambient space, space-time derivatives, strict ordering on a set

Part of the trusted statement surface; imports `Mathlib` only. Restates, token for token, the
definitions of the library file `BernoulliComparison/Interface/Setting.lean`.

* `E d` is `EuclideanSpace ℝ (Fin d)`. Space-time points are `p : E d × ℝ`, with `p.1` the space
  and `p.2` the time variable. The product `E d × ℝ` carries Mathlib's product (sup) metric; no
  statement below uses space-time balls.
* `gradₓ`, `lapₓ`, `dₜ` are Mathlib's `gradient` (`∇`), `InnerProductSpace.laplacian` (`Δ`) and
  `deriv`, applied to the time slice `y ↦ φ (y, t)` (for `∇`, `Δ`) or to the space slice
  `s ↦ φ (x, s)` (for `∂ₜ`) through `p = (x, t)`. They are only ever applied to `C^∞` functions.
* `PrecOn u v E F` is the strict ordering `u < v` on `E ∩ F`.
-/

open Set Filter Topology
open scoped Gradient Laplacian

namespace BernoulliComparison

/-- The ambient Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- Spatial gradient `∇ₓφ(x, t)`: the gradient of the time slice `y ↦ φ (y, t)` at `x`. -/
noncomputable def gradₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : E d :=
  ∇ (fun y ↦ φ (y, p.2)) p.1

/-- Spatial Laplacian `Δₓφ(x, t)`: the Laplacian of the time slice `y ↦ φ (y, t)` at `x`. -/
noncomputable def lapₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  Δ (fun y ↦ φ (y, p.2)) p.1

/-- Time derivative `∂ₜφ(x, t)`: the derivative of `s ↦ φ (x, s)` at `t`. -/
noncomputable def dₜ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  deriv (fun s ↦ φ (p.1, s)) p.2

section PrecOn

variable {X : Type*}

/-- `u ≺_E v` on `F`: `u < v` at every point of `E ∩ F`. -/
def PrecOn (u v : X → ℝ) (Eset F : Set X) : Prop := ∀ p ∈ Eset ∩ F, u p < v p

end PrecOn

end BernoulliComparison
