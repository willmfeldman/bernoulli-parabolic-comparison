import BernoulliComparison

/-!
# Solution: barrier solutions are viscosity solutions of the heat equation

Applies `IsParaRelaxedSub.subcaloric` and `IsParaSuper.supercaloric_on_pos`
(`BernoulliComparison/Touching/Caloric.lean`).
-/

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

theorem challenge_subcaloric {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    {S : Set (E d × ℝ)} (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) : IsCaloricSub (U ×ˢ I) u :=
  hsub.subcaloric hU hI

theorem challenge_supercaloric {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {v : E d × ℝ → ℝ}
    (hsup : IsParaSuper U Q I v) (hU : IsOpen U) (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) :
    IsCaloricSuper (posSetP v (U ×ˢ I)) v :=
  hsup.supercaloric_on_pos hU hI

end BernoulliComparison
