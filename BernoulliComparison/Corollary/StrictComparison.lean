/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Statements.Main

/-!
# Strict comparison for subsolutions

`para_strict_comparison` is the comparison principle for a (standard) viscosity subsolution `u` and
a supersolution `v`, with the order `≺` taken with `E = \overline{{u > 0}}`. It is proved from the
relaxed headline `para_relaxed_comparison` (`BernoulliComparison/Statements/Main.lean`):

* `IsParaSub.isParaRelaxedSub_closure`: a subsolution `u` gives the relaxed subsolution
  `(u, \overline{{u > 0}})`, `{u > 0}` computed in `U × I`.
* `closure_posSetP_Icc_eq`: for `u` continuous on `Ū × [0, T]`, `T > 0`, the closure of `{u > 0}`
  computed in `Ū × [0, T]` equals the closure of `{u > 0}` computed in `U × (0, T]`.
-/

@[expose] public section

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-- A (standard) viscosity subsolution `u` in `U × I` yields the relaxed subsolution
`(u, \overline{{u > 0}})`, with `{u > 0}` computed in `U × I`. The barrier clauses coincide
definitionally: `Prec u φ (U ×ˢ I) F` is `PrecOn u φ (closure (posSetP u (U ×ˢ I))) F`. -/
theorem IsParaSub.isParaRelaxedSub_closure {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ}
    {u : E d × ℝ → ℝ} (h : IsParaSub U Q I u) :
    IsParaRelaxedSub U Q I u (closure (posSetP u (U ×ˢ I))) :=
  ⟨h.1, h.2.1, isClosed_closure,
    by rw [← closure_prod_eq]; exact closure_mono fun _ hp ↦ hp.1, subset_closure, h.2.2⟩

/-- **Closure identity.** For `u` continuous on `Ū × [0, T]` and `T > 0`, the closure of `{u > 0}`
computed in `Ū × [0, T]` equals the closure of `{u > 0}` computed in `U × (0, T]`: every point of
`Ū × [0, T]` with `u > 0` is a limit of points of `U × (0, T]` (whose closure is `Ū × [0, T]`),
at which `u > 0` by continuity. -/
theorem closure_posSetP_Icc_eq {U : Set (E d)} {T : ℝ} {u : E d × ℝ → ℝ} (hT : 0 < T)
    (hu : ContinuousOn u (closure U ×ˢ Icc 0 T)) :
    closure (posSetP u (closure U ×ˢ Icc 0 T)) = closure (posSetP u (U ×ˢ Ioc 0 T)) := by
  have hsub : U ×ˢ Ioc 0 T ⊆ closure U ×ˢ Icc 0 T :=
    prod_mono subset_closure Ioc_subset_Icc_self
  refine subset_antisymm (closure_minimal ?_ isClosed_closure)
    (closure_mono fun p hp ↦ ⟨hsub hp.1, hp.2⟩)
  rintro p ⟨hpD, hpos⟩
  have hcl : closure (U ×ˢ Ioc 0 T) = closure U ×ˢ Icc 0 T := by
    rw [closure_prod_eq, closure_Ioc hT.ne]
  have hev : ∀ᶠ q in 𝓝[closure U ×ˢ Icc 0 T] p, 0 < u q :=
    (continuousWithinAt_const.eventually_lt (hu p hpD) hpos)
  obtain ⟨O, hOo, hpO, hOsub⟩ := mem_nhdsWithin.1 hev
  rw [mem_closure_iff_nhds]
  intro t ht
  rw [← hcl] at hpD
  obtain ⟨q, ⟨hqt, hqO⟩, hq⟩ := mem_closure_iff_nhds.1 hpD (t ∩ O) (inter_mem ht (hOo.mem_nhds hpO))
  exact ⟨q, hqt, hq, hOsub ⟨hqO, hsub hq⟩⟩

/-- **Strict comparison.** Let `U` be bounded and open, `Q` Lipschitz on `Ū` with a positive lower
bound, `T > 0`, and `u, v ∈ C(Ū × [0, T])` respectively a viscosity subsolution and a viscosity
supersolution (barrier definition, `IsParaSub`, `IsParaSuper`) of `∂ₜu = Δu` in `{u > 0}`,
`|∇u| = Q` on `∂{u > 0}`, in `U × (0, T]`. If `u ≺ v` on a neighbourhood `N` of the parabolic
boundary `∂_P(U × (0, T]) = (Ū × {0}) ∪ (∂U × [0, T])`, then `u ≺ v` on `Ū × [0, T]`.

Here `≺` is taken with `E = \overline{{u > 0}}`, `{u > 0}` computed in `Ū × [0, T]`. Proved from
`para_relaxed_comparison` via `closure_posSetP_Icc_eq` and `IsParaSub.isParaRelaxedSub_closure`. -/
theorem para_strict_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaSub U Q (Ioc 0 T) u) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    {N : Set (E d × ℝ)} (hN : N ∈ 𝓝ˢ (parBdry U 0 T))
    (hprec : Prec u v (closure U ×ˢ Icc 0 T) N) :
    Prec u v (closure U ×ˢ Icc 0 T) (closure U ×ˢ Icc 0 T) := by
  unfold Prec at hprec ⊢
  rw [closure_posSetP_Icc_eq hT hu] at hprec ⊢
  exact para_relaxed_comparison hU hUb hQ hQpos hT hu hv hsub.isParaRelaxedSub_closure hsuper
    hN hprec

end BernoulliComparison
