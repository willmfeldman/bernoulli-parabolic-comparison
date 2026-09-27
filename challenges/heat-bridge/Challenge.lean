import Challenge.Parabolic
import Challenge.Crossing

/-!
# Challenge: barrier solutions are viscosity solutions of the heat equation

The solution classes of the parabolic Bernoulli problem are defined by comparison with smooth
strict barriers on cylinders (`Challenge/Parabolic.lean`). This challenge certifies that they
satisfy the heat equation in the standard viscosity sense, with `C^∞` test functions touching on
backward parabolic cylinders (`Challenge/Crossing.lean`). Let `U ⊆ ℝᵈ` be open and let the time
set `I ⊆ ℝ` contain a left neighbourhood of each of its points (e.g. `I = (0, T]`). For any `Q`:

* `challenge_subcaloric`: if `(u, E)` is a relaxed subsolution in `U × I`, then `u` is a
  viscosity subsolution of the heat equation in all of `U × I`, including the zero set of `u`.
* `challenge_supercaloric`: if `v` is a supersolution in `U × I`, then `v` is a viscosity
  supersolution of the heat equation in its positivity set `{v > 0} ∩ (U × I)`.

Neither statement involves the free-boundary condition `Q` in its conclusion: the content is that
the barrier definitions encode the heat equation in the interior of the positive phase (and, for
subsolutions, across the zero set).
-/

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-- **Relaxed subsolutions are subcaloric.** If `(u, E)` is a relaxed subsolution of the
parabolic Bernoulli problem in `U × I`, with `U` open and `I` containing a left neighbourhood of
each of its points, then `u` is a viscosity subsolution of the heat equation in `U × I`. -/
theorem challenge_subcaloric {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    {S : Set (E d × ℝ)} (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) : IsCaloricSub (U ×ˢ I) u := by
  sorry

/-- **Supersolutions are supercaloric where positive.** If `v` is a supersolution of the
parabolic Bernoulli problem in `U × I`, with `U` open and `I` containing a left neighbourhood of
each of its points, then `v` is a viscosity supersolution of the heat equation in
`{v > 0} ∩ (U × I)`. -/
theorem challenge_supercaloric {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {v : E d × ℝ → ℝ}
    (hsup : IsParaSuper U Q I v) (hU : IsOpen U) (hI : ∀ t ∈ I, I ∈ 𝓝[≤] t) :
    IsCaloricSuper (posSetP v (U ×ˢ I)) v := by
  sorry

end BernoulliComparison
