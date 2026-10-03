module

public import Mathlib

@[expose] public section

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

/-!
# Challenge vocabulary: barrier (comparison) solutions of the parabolic Bernoulli problem

Part of the trusted statement surface; imports `Mathlib` only (earlier in this file).
Restates, token for token, the definitions of the library file
`BernoulliComparison/Interface/Parabolic.lean` that the challenge statements use.

The free boundary problem is

  `∂ₜu = Δu` in `{u > 0}`,  `|∇u| = Q` on `∂{u > 0}`,  `u ≥ 0`,

in a space-time domain `U × I`. Solutions are defined by comparison with classical strict
barriers on test cylinders:

* a test cylinder is `V × (a, b]` with `V` open and bounded, `a < b`, and `V̄ × [a, b] ⊆ U × I`
  (`AdmissibleCyl`);
* a classical strict subsolution (`IsClassicalStrictParaSub`) is a `C^∞` function `φ` on all of
  space-time with `∂ₜφ - Δφ < 0` on `closure {φ > 0}` and `|∇φ| > Q` on `∂{φ > 0}`, both
  within `V̄ × [a, b]`; a classical strict supersolution reverses both strict inequalities;
* `u` is a supersolution (`IsParaSuper`) if it is continuous and nonnegative on `U × I` and no
  classical strict subsolution can cross it from below: whenever `φ ≺ u` on the parabolic
  boundary `∂_P(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])` of a test cylinder, also `φ ≺ u` in
  `V × (a, b]`. Here `φ ≺ u` means `φ < u` on `closure {φ > 0}` (`Prec`), so the barrier is
  compared with `u` on its own positivity set and not where it is negative;
* `u` is a subsolution (`IsParaSub`) symmetrically: `u ≺ φ` (that is, `u < φ` on
  `closure {u > 0}`) propagates from `∂_P(V × (a, b])` into `V × (a, b]` for every classical
  strict supersolution `φ`;
* a relaxed subsolution `(u, E)` (`IsParaRelaxedSub`) is the same with the positivity set of `u`
  replaced by a given closed set `E ⊆ Ū × Ī` containing `{u > 0}`: the ordering is `u < φ` on
  `E` (`PrecOn u φ E`). For `E = closure {u > 0}` this is exactly `IsParaSub`.

The positivity set `{φ > 0}` of a barrier, its closure and its boundary are taken in all of
space-time; the positivity set of `u` is taken inside the domain `U × I` (`posSetP`).
-/

open Set Filter Topology
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-- The cylinder `V × (a, b]`. -/
def cyl (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) := V ×ˢ Ioc a b

/-- The parabolic boundary `∂_P(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])`. -/
def parBdry (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) :=
  (closure V ×ˢ {a}) ∪ (frontier V ×ˢ Icc a b)

/-- `V × (a, b]` is a test cylinder compactly contained in `U × I`: `V` is open and bounded,
`a < b`, and `V̄ × [a, b] ⊆ U × I`. -/
def AdmissibleCyl (U : Set (E d)) (I : Set ℝ) (V : Set (E d)) (a b : ℝ) : Prop :=
  IsOpen V ∧ Bornology.IsBounded V ∧ a < b ∧ closure V ×ˢ Icc a b ⊆ U ×ˢ I

/-- The positivity set `{u > 0}` of `u` inside the domain `Ω`. -/
def posSetP (u : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Set (E d × ℝ) := {p ∈ Ω | 0 < u p}

/-- `u ≺ v` on `F`: `u < v` on `closure {u > 0} ∩ F`, with `{u > 0}` taken inside `Ω`. -/
def Prec (u v : E d × ℝ → ℝ) (Ω F : Set (E d × ℝ)) : Prop :=
  PrecOn u v (closure (posSetP u Ω)) F

/-- `φ` is a classical strict subsolution on `V̄ × [a, b]`: `φ` is `C^∞` on space-time,
`∂ₜφ - Δφ < 0` on `closure {φ > 0} ∩ (V̄ × [a, b])`, and `|∇φ| > Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. -/
def IsClassicalStrictParaSub (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), dₜ φ p - lapₓ φ p < 0) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), Q p.1 < ‖gradₓ φ p‖

/-- `φ` is a classical strict supersolution on `V̄ × [a, b]`: `φ` is `C^∞` on space-time,
`∂ₜφ - Δφ > 0` on `closure {φ > 0} ∩ (V̄ × [a, b])`, and `|∇φ| < Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. -/
def IsClassicalStrictParaSuper (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), 0 < dₜ φ p - lapₓ φ p) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), ‖gradₓ φ p‖ < Q p.1

/-- **Supersolution** in `U × I`. `u` is continuous and nonnegative on `U × I`, and for every
test cylinder `V × (a, b]` and every classical strict subsolution `φ` on `V̄ × [a, b]`, if
`φ < u` on `closure {φ > 0} ∩ ∂_P(V × (a, b])`, then `φ < u` on
`closure {φ > 0} ∩ (V × (a, b])`. -/
def IsParaSuper (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSub Q φ V a b → Prec φ u univ (parBdry V a b) →
        Prec φ u univ (cyl V a b)

/-- **Subsolution** in `U × I`. `u` is continuous and nonnegative on `U × I`, and for every
test cylinder `V × (a, b]` and every classical strict supersolution `φ` on `V̄ × [a, b]`, if
`u < φ` on `closure {u > 0} ∩ ∂_P(V × (a, b])`, then `u < φ` on
`closure {u > 0} ∩ (V × (a, b])`; here `{u > 0}` is taken inside `U × I`. -/
def IsParaSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → Prec u φ (U ×ˢ I) (parBdry V a b) →
        Prec u φ (U ×ˢ I) (cyl V a b)

/-- **Relaxed subsolution** `(u, E)` in `U × I`. `u` is continuous and nonnegative on `U × I`;
`E` is a closed subset of `Ū × Ī` containing `{u > 0}` (taken inside `U × I`); and for every
test cylinder `V × (a, b]` and every classical strict supersolution `φ` on `V̄ × [a, b]`, if
`u < φ` on `E ∩ ∂_P(V × (a, b])`, then `u < φ` on `E ∩ (V × (a, b])`. -/
def IsParaRelaxedSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧ IsClosed Eset ∧
    Eset ⊆ closure U ×ˢ closure I ∧ posSetP u (U ×ˢ I) ⊆ Eset ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → PrecOn u φ Eset (parBdry V a b) →
        PrecOn u φ Eset (cyl V a b)

end BernoulliComparison
