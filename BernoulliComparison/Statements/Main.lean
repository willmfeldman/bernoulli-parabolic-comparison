/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Parabolic
public import BernoulliComparison.Main.Headline

/-!
# Headline statement: comparison for relaxed subsolutions

`para_relaxed_comparison` is the comparison principle between a relaxed subsolution `(u, E)`
(`IsParaRelaxedSub`) and a viscosity supersolution `v` (`IsParaSuper`), with the strict ordering
`≺_E`. Its proof is the term `Main.para_relaxed_comparison` in
`BernoulliComparison/Main/Headline.lean`, which has the same statement.

The strict comparison `para_strict_comparison` for standard subsolutions is derived from it in
`BernoulliComparison/Corollary/StrictComparison.lean`.
-/

@[expose] public section

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-- **Comparison principle for relaxed subsolutions.**
Let `U` be open and bounded, `Q` Lipschitz on `Ū` with a positive lower bound, `T > 0`, and
`u, v ∈ C(Ū × [0, T])`. Let `(u, E)` be a relaxed viscosity subsolution (`IsParaRelaxedSub`) and
`v` a viscosity supersolution (`IsParaSuper`) of `∂ₜu = Δu` in `{u > 0}`, `|∇u| = Q` on
`∂{u > 0}`, in `U × (0, T]`. If `u ≺_E v` on a neighbourhood `N` of the parabolic boundary
`∂_P(U × (0, T]) = (Ū × {0}) ∪ (∂U × [0, T])`, then `u ≺_E v` on `Ū × [0, T]`.

Faithfulness notes.
* `E ⊆ Ū × [0, T]` is not a separate hypothesis: it is part of `hsub`
  (`IsParaRelaxedSub` requires `E` closed with `E ⊆ closure U ×ˢ closure (Ioc 0 T)`, and
  `closure (Ioc 0 T) = Icc 0 T` as `0 < T`), as is `{u > 0} ⊆ E` for `{u > 0}` computed in
  `U × (0, T]`.
* The conclusion is strict (`u < v`) on `E ∩ (Ū × [0, T])` only, not `u ≤ v` everywhere;
  off `E` one has `u ≤ 0 ≤ v` in `U × (0, T]` anyway.
* `U` need not be connected.
* Both functions are assumed continuous on `Ū × [0, T]`, not only on `U × (0, T]`. -/
theorem para_relaxed_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
    {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T) :=
  Main.para_relaxed_comparison hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec

end BernoulliComparison
