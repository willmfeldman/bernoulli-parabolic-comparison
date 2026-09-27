/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Parabolic
public import ParabolicBasic.MainTheorems

/-!
# Classical solvability of the heat Dirichlet problem on a ball cylinder

`Heat.caloric_dirichlet_ball`: the first boundary value problem for the heat equation on the
cylinder `B_ρ(x₀) × (a, b)` with continuous data on the parabolic boundary is solvable, with a
solution continuous on `closedBall x₀ ρ × [a, b]` and `C^∞` and caloric in the *open* cylinder.
It is the only classical analytic input of the proof, used for the caloric replacement in
`Contact/ZeroContact.lean`. It is proved in the dependency `parabolic_basic_theory`
(`ParabolicBasic.caloric_dirichlet_ball`, whose statement is token-identical); the theorems
`parabolicBasic_*_eq` at the end check by `rfl` that the definitions occurring in the statement
(`E`, `gradₓ`, `lapₓ`, `dₜ`, `cyl`, `parBdry`) agree with that package's.

## Design notes

* **Top-time smoothness.** Only smoothness on the open cylinder `ball x₀ ρ ×ˢ Ioo a b` is claimed.
  The only use compares `h` (and `h + σP`) with sub/supercaloric functions via
  `Heat.domain_comparison_sub/super` on `Ω = B_ρ × (a, b)`. That argument (penalization
  `ε / (b - t)`) places every maximum point strictly before the top time, so it uses only
  (i) smoothness and the heat equation in the open set `Ω` and (ii) continuity on `closure Ω`.
* **Smoothness order.** `ContDiffOn ℝ ∞` (i.e. `C^∞`, `(⊤ : ℕ∞)`), **not** `ContDiffOn ℝ ⊤`: in
  current Mathlib `⊤ : WithTop ℕ∞` is `ω` (real-analytic), and caloric functions are in general
  not real-analytic in time (in `d = 1`, `Σₖ g⁽ᵏ⁾(t) x²ᵏ / (2k)!` with `g` of Gevrey class 2 but not
  analytic is caloric), so `⊤` would make the statement false.
* **Dimension.** The statement holds for every `d` (for `d = 0` the lateral boundary is empty and
  `h` is the constant `g (0, a)`), so no `d ≥ 1` hypothesis is imposed.
* Continuity of `g` is required only on `parBdry`, and `h = g` is asserted only there.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Ch. 3
  (the first boundary value problem in general domains), together with interior regularity of
  solutions of the heat equation.
* N. A. Watson, *Introduction to Heat Potential Theory*, AMS Math. Surveys Monogr. 182, 2012
  (Perron–Wiener–Brelot solution of the Dirichlet problem, regularity of cylinder boundary points).
* G. M. Lieberman, *Second Order Parabolic Differential Equations*, World Scientific, 1996,
  Ch. III (barriers; the exterior cone condition makes lateral points regular).

For a ball cylinder every point of the parabolic boundary is regular: lateral points by the exterior
ball (hence exterior cone) condition, and the points of the initial face (including its rim) are
regular as well (Watson 2012).
-/

@[expose] public section

open Set Metric
open scoped ContDiff

namespace BernoulliComparison

namespace Heat

variable {d : ℕ}

/-- **Caloric replacement on a ball cylinder.** Let `x₀ ∈ ℝᵈ`, `ρ > 0`, `a < b`, and let `g` be
continuous on the parabolic boundary `∂ₚ(B_ρ(x₀) × (a, b]) = (closedBall x₀ ρ × {a}) ∪
(sphere x₀ ρ × [a, b])`. Then there is `h`, continuous on `closedBall x₀ ρ × [a, b]`, `C^∞` on the
open cylinder `B_ρ(x₀) × (a, b)`, with `∂ₜh = Δh` there and `h = g` on the parabolic boundary.

Classical (Friedman 1964, Ch. 3; Watson 2012; Lieberman 1996, Ch. III); proved in
`parabolic_basic_theory` (`ParabolicBasic.caloric_dirichlet_ball`). -/
theorem caloric_dirichlet_ball (x₀ : E d) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (hab : a < b)
    {g : E d × ℝ → ℝ} (hg : ContinuousOn g (parBdry (ball x₀ ρ) a b)) :
    ∃ h : E d × ℝ → ℝ, ContinuousOn h (closedBall x₀ ρ ×ˢ Icc a b) ∧
      ContDiffOn ℝ ∞ h (ball x₀ ρ ×ˢ Ioo a b) ∧
      (∀ p ∈ ball x₀ ρ ×ˢ Ioo a b, dₜ h p = lapₓ h p) ∧
      EqOn h g (parBdry (ball x₀ ρ) a b) := by
  exact ParabolicBasic.caloric_dirichlet_ball x₀ hρ hab hg

/-! The definitions of `parabolic_basic_theory` occurring in the statement agree with ours by
`rfl`. -/
theorem parabolicBasic_E_eq (d : ℕ) : ParabolicBasic.E d = E d := rfl
theorem parabolicBasic_gradₓ_eq : @ParabolicBasic.gradₓ d = @gradₓ d := rfl
theorem parabolicBasic_lapₓ_eq : @ParabolicBasic.lapₓ d = @lapₓ d := rfl
theorem parabolicBasic_dₜ_eq : @ParabolicBasic.dₜ d = @dₜ d := rfl
theorem parabolicBasic_cyl_eq : @ParabolicBasic.cyl d = @cyl d := rfl
theorem parabolicBasic_parBdry_eq : @ParabolicBasic.parBdry d = @parBdry d := rfl

end Heat

end BernoulliComparison
