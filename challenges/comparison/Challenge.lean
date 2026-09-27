import Challenge.Parabolic

/-!
# Challenge: comparison for the parabolic Bernoulli problem

Trusted statement surface for the comparison principle for

  `∂ₜu = Δu` in `{u > 0}`,  `|∇u| = Q` on `∂{u > 0}`

in `U × (0, T]`, between a supersolution and a (relaxed) subsolution in the barrier sense. The
project vocabulary is restated inline, token for token, in `Challenge/Setting.lean` (the space
`E d`, the operators `gradₓ`, `lapₓ`, `dₜ`, and the ordering `PrecOn`) and
`Challenge/Parabolic.lean` (cylinders, parabolic boundaries, classical strict barriers, and the
solution notions `IsParaSuper`, `IsParaSub`, `IsParaRelaxedSub`), which together import `Mathlib`
only. Read `Challenge/Parabolic.lean` first: its module docstring explains the definitions.

Common hypotheses of both statements:

* `U ⊆ ℝᵈ` is open and bounded; `T > 0`;
* `Q` is Lipschitz on `Ū` and bounded below on `Ū` by a positive constant;
* `u` and `v` are continuous on `Ū × [0, T]` (the solution notions only require continuity on
  `U × (0, T]`);
* the ordering holds on some neighbourhood `N` of the parabolic boundary
  `∂_P(U × (0, T]) = (Ū × {0}) ∪ (∂U × [0, T])` (a set `N` with `N ∈ 𝓝ˢ (parBdry U 0 T)`).

The conclusion is the strict ordering on `Ū × [0, T]`. It is strict only on the ordering set:
`u < v` on `E ∩ (Ū × [0, T])` in the relaxed form and on `closure {u > 0} ∩ (Ū × [0, T])` in the
standard form. Off that set `u ≤ 0 ≤ v` holds in `U × (0, T]` by the definitions.
-/

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-- **Comparison principle, relaxed form.** Let `U ⊆ ℝᵈ` be open and bounded, `Q` Lipschitz on
`Ū` with a positive lower bound on `Ū`, `T > 0`, and `u, v` continuous on `Ū × [0, T]`. Let
`(u, E)` be a relaxed subsolution and `v` a supersolution in `U × (0, T]`. If `u < v` on
`E ∩ N` for a neighbourhood `N` of the parabolic boundary `∂_P(U × (0, T])`, then `u < v` on
`E ∩ (Ū × [0, T])`.

`E` is part of the data of the relaxed subsolution: `hsub` requires `E` to be closed, contained
in `Ū × [0, T]` (`closure (Ioc 0 T) = Icc 0 T` as `T > 0`), and to contain `{u > 0}`. -/
theorem challenge_relaxed_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T) := by
  sorry

/-- **Comparison principle, standard form.** Same setting, with `u` a subsolution. Write
`P = closure {u > 0}`, with `{u > 0}` taken in `Ū × [0, T]`. If `u < v` on `P ∩ N` for a
neighbourhood `N` of the parabolic boundary `∂_P(U × (0, T])`, then `u < v` on
`P ∩ (Ū × [0, T])`.

This is a corollary of `challenge_relaxed_comparison` with `E = P` (a subsolution `u` makes
`(u, P)` a relaxed subsolution), so it adds little independent coverage. -/
theorem challenge_strict_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaSub U Q (Ioc 0 T) u) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    {N : Set (E d × ℝ)} (hN : N ∈ 𝓝ˢ (parBdry U 0 T))
    (hprec : Prec u v (closure U ×ˢ Icc 0 T) N) :
    Prec u v (closure U ×ˢ Icc 0 T) (closure U ×ˢ Icc 0 T) := by
  sorry

end BernoulliComparison
