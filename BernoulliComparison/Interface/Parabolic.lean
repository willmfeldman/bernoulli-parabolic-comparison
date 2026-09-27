/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Setting

/-!
# Parabolic solution notions for the Bernoulli problem

Barrier (comparison) definitions of viscosity sub- and supersolutions, and of relaxed
subsolutions, for the parabolic Bernoulli problem
`∂ₜu = Δu` in `{u > 0}`, `|∇u| = Q` on `∂{u > 0}`.
A function is tested against classical strict sub/supersolutions on admissible cylinders: if the
test function is strictly ordered with `u` on the parabolic boundary, the strict order must
persist inside the cylinder.

Space-time points are `p : E d × ℝ`. A general time set `I : Set ℝ` is used (typically
`(0, T]` or `(0, ∞)`); `U ×ˢ I` is the space-time domain.

## Main definitions

* `cyl`, `parBdry`, `AdmissibleCyl`: parabolic cylinders, parabolic boundaries, and admissible
  cylinders `V × (a, b] ⊂⊂ U × I`.
* `IsClassicalStrictParaSub`, `IsClassicalStrictParaSuper`: classical strict sub/supersolutions.
  The test function is globally smooth, and `{φ > 0}`, its closure and its boundary are taken in
  all of space-time.
* `IsParaSuper`, `IsParaSub`, `IsParaSolution`: parabolic viscosity super/sub/solutions.
* `IsParaRelaxedSub`, `IsParaRelaxedSolution`: parabolic relaxed subsolutions/solutions `(u, E)`,
  where the ordering is required only on a closed set `E ⊇ {u > 0}`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Cylinders and parabolic boundaries -/

/-- The cylinder `V × (a, b]`. -/
def cyl (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) := V ×ˢ Ioc a b

/-- The parabolic boundary `∂_P(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])`. -/
def parBdry (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) :=
  (closure V ×ˢ {a}) ∪ (frontier V ×ˢ Icc a b)

/-- `V × (a, b] ⊂⊂ U × I` is an admissible test cylinder: `V` is open and bounded, `a < b`, and
`closure (V × (a, b]) = V̄ × [a, b] ⊆ U × I`. -/
def AdmissibleCyl (U : Set (E d)) (I : Set ℝ) (V : Set (E d)) (a b : ℝ) : Prop :=
  IsOpen V ∧ Bornology.IsBounded V ∧ a < b ∧ closure V ×ˢ Icc a b ⊆ U ×ˢ I

/-! ### Positivity sets and the ordering `≺` -/

/-- The space-time positivity set `{u > 0}` inside the domain `Ω`. -/
def posSetP (u : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Set (E d × ℝ) := {p ∈ Ω | 0 < u p}

/-- The strict ordering `u ≺ v` on `F`: `u ≺_E v` on `F` with `E = \overline{{u > 0}}`, where
`{u > 0}` is taken inside the domain `Ω` of `u`. -/
def Prec (u v : E d × ℝ → ℝ) (Ω F : Set (E d × ℝ)) : Prop :=
  PrecOn u v (closure (posSetP u Ω)) F

/-! ### Classical strict sub/supersolutions -/

/-- Classical strict subsolution of the parabolic Bernoulli problem on `V̄ × [a, b]`: `φ` is
globally smooth, `∂ₜφ - Δφ < 0` on `\overline{{φ > 0}} ∩ (V̄ × [a, b])` and `|∇φ| > Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. The sets `{φ > 0}`, its closure and its boundary are taken in all of
space-time, so the conditions only involve `φ` near `V̄ × [a, b]`.
Here `∞` in `ContDiff ℝ ∞` is `C^∞` (not `⊤`, which is analyticity). -/
def IsClassicalStrictParaSub (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), dₜ φ p - lapₓ φ p < 0) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), Q p.1 < ‖gradₓ φ p‖

/-- Classical strict supersolution of the parabolic Bernoulli problem on `V̄ × [a, b]`: `φ` is
globally smooth, `∂ₜφ - Δφ > 0` on `\overline{{φ > 0}} ∩ (V̄ × [a, b])` and `|∇φ| < Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. -/
def IsClassicalStrictParaSuper (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), 0 < dₜ φ p - lapₓ φ p) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), ‖gradₓ φ p‖ < Q p.1

/-! ### Parabolic viscosity solutions -/

/-- Barrier definition of viscosity supersolutions. `u ∈ C(U × I; [0, ∞))` is a supersolution
of the parabolic Bernoulli problem if, for every admissible cylinder `V × (a, b] ⊂⊂ U × I` and
every classical strict subsolution `φ` on `V̄ × [a, b]` with `φ ≺ u` on `∂_P(V × (a, b])`,
also `φ ≺ u` in `V × (a, b]`. (`φ ≺ u` uses `\overline{{φ > 0}}`, computed in all of space-time.) -/
def IsParaSuper (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSub Q φ V a b → Prec φ u univ (parBdry V a b) →
        Prec φ u univ (cyl V a b)

/-- Barrier definition of viscosity subsolutions. `u ∈ C(U × I; [0, ∞))` is a subsolution
of the parabolic Bernoulli problem if, for every admissible cylinder `V × (a, b] ⊂⊂ U × I` and
every classical strict supersolution `φ` on `V̄ × [a, b]` with `u ≺ φ` on `∂_P(V × (a, b])`,
also `u ≺ φ` in `V × (a, b]`. (`u ≺ φ` uses `\overline{{u > 0}}`, `{u > 0} ⊆ U × I`.) -/
def IsParaSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → Prec u φ (U ×ˢ I) (parBdry V a b) →
        Prec u φ (U ×ˢ I) (cyl V a b)

/-- Parabolic viscosity solution: both a super- and a subsolution. -/
def IsParaSolution (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  IsParaSuper U Q I u ∧ IsParaSub U Q I u

/-! ### Parabolic relaxed subsolutions -/

/-- Barrier definition of relaxed subsolutions. For `u ∈ C(U × I; [0, ∞))` and `E` closed,
contained in `Ū × Ī`, with `{u > 0} ⊆ E`, `(u, E)` is a relaxed subsolution if, for every
admissible cylinder `V × (a, b] ⊂⊂ U × I` and classical strict supersolution `φ` on
`V̄ × [a, b]` with `u ≺_E φ` on `∂_P(V × (a, b])`, also `u ≺_E φ` in `V × (a, b]`. -/
def IsParaRelaxedSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧ IsClosed Eset ∧
    Eset ⊆ closure U ×ˢ closure I ∧ posSetP u (U ×ˢ I) ⊆ Eset ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → PrecOn u φ Eset (parBdry V a b) →
        PrecOn u φ Eset (cyl V a b)

/-- `(u, E)` is a relaxed viscosity solution: `u` is a (standard) supersolution and `(u, E)` is a
relaxed subsolution. -/
def IsParaRelaxedSolution (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  IsParaSuper U Q I u ∧ IsParaRelaxedSub U Q I u Eset

end BernoulliComparison
