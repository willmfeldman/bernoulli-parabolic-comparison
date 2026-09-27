import Challenge.Setting

/-!
# Challenge vocabulary: barrier (comparison) solutions of the parabolic Bernoulli problem

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Setting`).
Restates, token for token, definitions of the library file
`BernoulliComparison/Interface/Parabolic.lean`.

The free boundary problem is `∂ₜu = Δu` in `{u > 0}`, `|∇u| = Q(x)` on `∂{u > 0}`, for
`u ≥ 0` on a space-time domain `U × I`. Solutions are defined by comparison with smooth strict
barriers on small cylinders, in the spirit of Caffarelli's definition for the elliptic problem:

* a *classical strict subsolution* on `V̄ × [a, b]` is a globally `C^∞` function `φ` with
  `∂ₜφ - Δφ < 0` on the closure of `{φ > 0}` and `|∇φ| > Q` on the free boundary `∂{φ > 0}`
  (both restricted to `V̄ × [a, b]`); a *classical strict supersolution* has the reverse strict
  inequalities. The sets `{φ > 0}`, its closure and its frontier are taken in all of
  space-time.
* `u` is a *supersolution* (`IsParaSuper`) if, for every admissible cylinder
  `V × (a, b] ⊂⊂ U × I` and every classical strict subsolution `φ` there, `φ ≺ u` on the
  parabolic boundary implies `φ ≺ u` in the cylinder. Here `φ ≺ u on F` means `φ < u` at the
  points of `F` in the closure of `{φ > 0}`.
* `(u, E)` is a *relaxed subsolution* (`IsParaRelaxedSub`) if `E` is a closed set containing
  `{u > 0}`, and for every admissible cylinder and classical strict supersolution `φ`,
  `u < φ` on `E ∩ ∂ₚ` implies `u < φ` on `E ∩ (V × (a, b])`.

The unused definitions `IsParaSub`, `IsParaSolution` and `IsParaRelaxedSolution` of the library
file are not restated.
-/

open Set Filter Topology
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-- The cylinder `V × (a, b]`. -/
def cyl (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) := V ×ˢ Ioc a b

/-- The parabolic boundary `∂ₚ(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])`. -/
def parBdry (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) :=
  (closure V ×ˢ {a}) ∪ (frontier V ×ˢ Icc a b)

/-- `V × (a, b]` is an admissible test cylinder in `U × I`: `V` is open and bounded, `a < b`, and
the closed cylinder `V̄ × [a, b]` lies in `U × I`. -/
def AdmissibleCyl (U : Set (E d)) (I : Set ℝ) (V : Set (E d)) (a b : ℝ) : Prop :=
  IsOpen V ∧ Bornology.IsBounded V ∧ a < b ∧ closure V ×ˢ Icc a b ⊆ U ×ˢ I

/-- The positivity set `{p ∈ Ω | u p > 0}`. -/
def posSetP (u : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Set (E d × ℝ) := {p ∈ Ω | 0 < u p}

/-- `u ≺ v on F`: `u < v` at the points of `F` in the closure of the positivity set of `u`
(taken inside `Ω`). -/
def Prec (u v : E d × ℝ → ℝ) (Ω F : Set (E d × ℝ)) : Prop :=
  PrecOn u v (closure (posSetP u Ω)) F

/-- Classical strict subsolution on `V̄ × [a, b]`: `φ` is `C^∞` on space-time,
`∂ₜφ - Δₓφ < 0` on `closure {φ > 0} ∩ (V̄ × [a, b])`, and `|∇ₓφ| > Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. -/
def IsClassicalStrictParaSub (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), dₜ φ p - lapₓ φ p < 0) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), Q p.1 < ‖gradₓ φ p‖

/-- Classical strict supersolution on `V̄ × [a, b]`: `φ` is `C^∞` on space-time,
`∂ₜφ - Δₓφ > 0` on `closure {φ > 0} ∩ (V̄ × [a, b])`, and `|∇ₓφ| < Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. -/
def IsClassicalStrictParaSuper (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), 0 < dₜ φ p - lapₓ φ p) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), ‖gradₓ φ p‖ < Q p.1

/-- Supersolution of the parabolic Bernoulli problem in `U × I`: `u` is continuous and
nonnegative on `U × I`, and for every admissible cylinder `V × (a, b]` and every classical strict
subsolution `φ` on `V̄ × [a, b]`, `φ ≺ u` on the parabolic boundary implies `φ ≺ u` in
`V × (a, b]`. -/
def IsParaSuper (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSub Q φ V a b → Prec φ u univ (parBdry V a b) →
        Prec φ u univ (cyl V a b)

/-- Relaxed subsolution `(u, E)` of the parabolic Bernoulli problem in `U × I`: `u` is continuous
and nonnegative on `U × I`; `E` is closed, contained in `Ū × Ī`, and contains `{u > 0}`; and for
every admissible cylinder `V × (a, b]` and every classical strict supersolution `φ` on
`V̄ × [a, b]`, `u < φ` on `E ∩ ∂ₚ(V × (a, b])` implies `u < φ` on `E ∩ (V × (a, b])`. -/
def IsParaRelaxedSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧ IsClosed Eset ∧
    Eset ⊆ closure U ×ˢ closure I ∧ posSetP u (U ×ˢ I) ⊆ Eset ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → PrecOn u φ Eset (parBdry V a b) →
        PrecOn u φ Eset (cyl V a b)

end BernoulliComparison
