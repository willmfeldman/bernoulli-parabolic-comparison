# Comparison for the Parabolic Bernoulli Problem

`BernoulliComparison` is a Lean 4 formalization of the comparison principle for
the parabolic Bernoulli (one-phase free boundary) problem

    ∂ₜu = Δu  in {u > 0},      |∇u| = Q(x)  on ∂{u > 0},

in a cylinder `U × (0, T]`, with `U ⊆ ℝᵈ` bounded and open and `Q` Lipschitz
and bounded below by a positive constant. Sub- and supersolutions are defined
by comparison with classical strict barriers, and the subsolution may be
*relaxed*: a pair `(u, E)` whose closed set `E` contains the positivity set
`{u > 0}`. The approximately 11,900 lines of Lean source are `sorry`-free and
introduce no axioms: the headline theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`.

## Main theorems

The root module `BernoulliComparison` imports the whole library.

| Declaration (`BernoulliComparison.…`) | Statement |
|---|---|
| `para_relaxed_comparison` | Let `(u, E)` be a relaxed subsolution and `v` a supersolution in `U × (0, T]`, both continuous on `Ū × [0, T]`. If `u < v` on `E ∩ N` for a neighbourhood `N` of the parabolic boundary `(Ū × {0}) ∪ (∂U × [0, T])`, then `u < v` on `E ∩ (Ū × [0, T])` |
| `para_strict_comparison` | The same for a (standard) subsolution `u`, with `E` the closure of `{u > 0}` |

The statement of the first, from `BernoulliComparison/Statements/Main.lean`:

```lean
theorem para_relaxed_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
    {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T)
```

The solution notions are defined in `BernoulliComparison/Interface/Parabolic.lean`.
A classical strict subsolution on `V̄ × [a, b]` is a `C^∞` function `φ` with
`∂ₜφ − Δφ < 0` on the closure of `{φ > 0}` and `|∇φ| > Q` on `∂{φ > 0}`.
Take any admissible cylinder `V × (a, b]` compactly inside the domain and any
such `φ`. A continuous `v ≥ 0` is a supersolution if `φ < v` on the closure of
`{φ > 0}` along the parabolic boundary of the cylinder implies the same inside
the cylinder. Subsolutions are defined symmetrically, with classical strict
supersolutions. For relaxed subsolutions the order is tested on `E` rather than
on the closure of `{u > 0}`.

## Proof

The proof follows the approach of Kim (2003). Its steps are:

1. **Reductions.** A margin `u + θ ≤ v` near the parabolic boundary, and a
   multiplicative gap between the free boundary coefficients of the two
   functions, obtained by rescaling `u` and `v` and using the Lipschitz
   continuity of `Q`.
2. **Regularization.** A sup-convolution of `u` and an inf-convolution of `v`,
   first over a spatial disk and then over a backward space-time ball. The
   convolved pair consists of a relaxed subsolution and a supersolution
   (`IsParaRelaxedSub.supConv`, `IsParaSuper.infConv`); the kernels give
   interior and exterior space-time balls at a contact point.
3. **First contact.** If the convolved functions cross, there is a first
   contact point. There both functions vanish (by caloric replacement, using
   the solvability of the heat Dirichlet problem on a ball cylinder), and the
   contact point carries two unit space-time normals.
4. **Non-polar normals.** If both normals have non-zero spatial parts,
   explicit barriers give a lower growth rate for the subsolution and an upper
   one for the supersolution along one spatial axis. The gap from step 1 makes
   the two rates incompatible (`NonPolar.no_nonpolar`).
5. **Polar normals.** Contact points with a purely temporal normal are
   excluded by a reduction to the south pole, and then by one comparison with
   an explicit self-similar barrier at the rim of the spatial convolution disk
   for each of the two north-pole cases (`Polar.no_polar`).

The proof differs from Kim (2003) in three places:
- In the non-polar case, the strict inequality between the two rates comes
  from the gap in `Q` instead of Hopf's lemma.
- The rates are compared along one axis, so the collinearity of the two
  normals is not needed.
- Kim's treatment of the polar case (Lemma 2.3) uses ellipsoidal kernels and
  a parabolic rescaling. Here the kernels are a disk followed by a backward
  ball, and each polar case has its own barrier argument.

The barrier notions are related to the usual touching (test-function)
notions in `BernoulliComparison/Touching/`: the function part of a relaxed
subsolution is a viscosity subsolution of the heat equation, and a
supersolution is a viscosity supersolution of the heat equation in `{v > 0}`
(`IsParaRelaxedSub.subcaloric`, `IsParaSuper.supercaloric_on_pos`).

## Building

This project uses the pinned Lean toolchain in `lean-toolchain` and the
dependency revisions in `lake-manifest.json`. From a checkout:

```bash
lake exe cache get
lake build
```

The Mathlib cache covers Mathlib only. The other dependencies below are
compiled from source on the first build.

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.30.0`.
- [parabolic-basic-theory](https://github.com/willmfeldman/parabolic-basic-theory)
  [`v0.1.0`](https://github.com/willmfeldman/parabolic-basic-theory/releases/tag/v0.1.0)
  (library `ParabolicBasic`). It supplies the classical solvability of the heat
  Dirichlet problem on ball cylinders (`ParabolicBasic.caloric_dirichlet_ball`),
  used in step 3; see `BernoulliComparison/Heat/Dirichlet.lean`.
- [viscosity-solution-theory](https://github.com/willmfeldman/viscosity-solution-theory)
  `v0.2.0` and
  [aleksandrov-differentiability](https://github.com/willmfeldman/aleksandrov-differentiability),
  dependencies of `ParabolicBasic`.

## Formalization metadata

[formalization.yaml](formalization.yaml) records the headline declarations,
their informal statements and expected axioms, and the comparator challenges.
The directory [challenges/](challenges/) contains standalone
[Comparator](https://github.com/leanprover/comparator) workspaces. Each
`Challenge.lean` restates a theorem and all of its vocabulary using Mathlib
only, and each `Solution.lean` proves it from the library. See
[challenges/README.md](challenges/README.md) for the challenge set, its scope,
and the verification procedure.

## Layout

- `BernoulliComparison/Interface/`: the setting (`E d`, the slice derivatives
  `gradₓ`, `lapₓ`, `dₜ`, cylinders and parabolic boundaries) and the barrier
  definitions of sub-, super- and relaxed subsolutions.
- `BernoulliComparison/Statements/`, `Corollary/`: the headline theorems.
- `BernoulliComparison/Barrier/`: structural lemmas (scaling, translation,
  monotonicity in `Q`, margin at the parabolic boundary).
- `BernoulliComparison/Convolution/`: sup- and inf-convolutions and their
  preservation of sub- and supersolutions.
- `BernoulliComparison/Touching/`, `Heat/`: touching notions, viscosity
  solutions of the heat equation, and comparison with caloric functions.
- `BernoulliComparison/Crossing/`, `Contact/`: the regularized configuration,
  the first crossing time, and the structure of first contact points.
- `BernoulliComparison/Barriers/`: explicit radial, paraboloid, slope and
  self-similar barriers.
- `BernoulliComparison/NonPolar/`, `Polar/`: exclusion of the two kinds of
  contact points.
- `BernoulliComparison/Main/`: assembly of the proof (including `d = 0`).
- `challenges/`, `scripts/`, `.github/workflows/`: comparator challenges and
  their verification tooling.

## References

- I. C. Kim, [*A free boundary problem arising in flame
  propagation*](https://doi.org/10.1016/S0022-0396(02)00195-X), J. Differential
  Equations 191 (2003), 470–489.
- A. Friedman, *Partial Differential Equations of Parabolic Type*,
  Prentice-Hall (1964).
- N. A. Watson, *Introduction to Heat Potential Theory*, AMS (2012).
- G. M. Lieberman, *Second Order Parabolic Differential Equations*, World
  Scientific (1996).

## License and citation

The project is released under the [Apache License 2.0](LICENSE). If you use
this work, please cite it using [CITATION.cff](CITATION.cff).

The Lean code was developed with AI coding agents under human direction and
review; see `automation` in [formalization.yaml](formalization.yaml).
