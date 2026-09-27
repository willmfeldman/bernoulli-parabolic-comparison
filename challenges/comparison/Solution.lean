import BernoulliComparison

/-!
# Solution: comparison for the parabolic Bernoulli problem

Discharges the challenge through the library theorems
`BernoulliComparison.para_relaxed_comparison` and `BernoulliComparison.para_strict_comparison`.
-/

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

theorem challenge_relaxed_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T) :=
  para_relaxed_comparison hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec

theorem challenge_strict_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaSub U Q (Ioc 0 T) u) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    {N : Set (E d × ℝ)} (hN : N ∈ 𝓝ˢ (parBdry U 0 T))
    (hprec : Prec u v (closure U ×ˢ Icc 0 T) N) :
    Prec u v (closure U ×ˢ Icc 0 T) (closure U ×ˢ Icc 0 T) :=
  para_strict_comparison hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec

end BernoulliComparison
