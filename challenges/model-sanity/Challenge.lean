import Challenge.Parabolic

/-!
# Challenge: non-vacuity and sign-convention checks for the barrier solution classes

A sanity check, not coverage of the main results. It guards against solution classes that are
empty, trivially true, or carry the wrong sign. All functions are explicit, on `ℝᵈ × ℝ` for any
dimension `d`; the vocabulary is restated in `Challenge/Setting.lean` and
`Challenge/Parabolic.lean`, which import `Mathlib` only.

`challenge_model_sanity` is the conjunction of:

1. **An explicit strict supersolution barrier.** `φ(x, t) = 1 + t - |x|²` is a classical strict
   supersolution for `Q ≡ 3` on `B̄₂(0) × [0, 1]`: `∂ₜφ - Δφ = 1 + 2d > 0`, and on the free
   boundary `{|x|² = 1 + t}` one has `|∇φ| = 2|x| ≤ 2√2 < 3`. So the barrier class used in the
   definition of subsolutions is non-empty.
2. **The free-boundary clause of (1) is not vacuous.** For `d ≥ 1`, the free boundary
   `∂{φ > 0}` meets `B̄₂(0) × [0, 1]`.
3. **An explicit strict subsolution barrier.** `ψ(x, t) = 1 - |x|² - (2d + 1)t` is a classical
   strict subsolution for `Q ≡ 1` on `B̄₂(0) × [0, T_d]`, `T_d = 1/(4d + 2)`. Its positivity set
   is the shrinking ball `{|x|² < 1 - (2d + 1)t}`, and `∂ₜψ - Δψ = -1 < 0`. On the free boundary
   `|∇ψ| = 2|x| = 2√(1 - (2d + 1)t)`, which tends to `0` as the ball vanishes at `t = 1/(2d + 1)`;
   up to `T_d` one has `|x|² ≥ 1/2`, so `|∇ψ| ≥ √2 > 1`. So the barrier class used in the
   definition of supersolutions is non-empty, and the time restriction is genuinely needed.
4. **The free-boundary clause of (3) is not vacuous.** For `d ≥ 1`, the free boundary
   `∂{ψ > 0}` meets `B̄₂(0) × [0, T_d]`.
5. **Positive constants are supersolutions**, for every domain `U × I` and every `Q`.
6. **`(0, ∅)` is a relaxed subsolution**, for every domain `U × I` and every `Q`.
7. **Sign convention (negative test).** `v(x, t) = 1 - t/2` is **not** a supersolution in
   `B₂(0) × (0, 1]`, for any `Q`. It is positive there and `∂ₜv - Δv = -1/2 < 0`, so it is a
   strict subsolution of the heat equation. A definition with the time direction or the sign of
   the heat operator reversed would accept it.
-/

open Set Filter Topology Metric

namespace BernoulliComparison

/-- Non-vacuity and sign-convention checks; see the module docstring for the seven conjuncts. -/
theorem challenge_model_sanity (d : ℕ) :
    IsClassicalStrictParaSuper (fun _ ↦ 3) (fun p : E d × ℝ ↦ 1 + p.2 - ‖p.1‖ ^ 2)
        (ball 0 2) 0 1 ∧
      (0 < d → (frontier {p : E d × ℝ | 0 < 1 + p.2 - ‖p.1‖ ^ 2} ∩
        (closure (ball (0 : E d) 2) ×ˢ Icc 0 1)).Nonempty) ∧
      IsClassicalStrictParaSub (fun _ ↦ 1)
        (fun p : E d × ℝ ↦ 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2) (ball 0 2) 0 (1 / (4 * d + 2)) ∧
      (0 < d → (frontier {p : E d × ℝ | 0 < 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2} ∩
        (closure (ball (0 : E d) 2) ×ˢ Icc (0 : ℝ) (1 / (4 * d + 2)))).Nonempty) ∧
      (∀ (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (c : ℝ), 0 < c →
        IsParaSuper U Q I (fun _ ↦ c)) ∧
      (∀ (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ), IsParaRelaxedSub U Q I (fun _ ↦ 0) ∅) ∧
      ∀ Q : E d → ℝ, ¬ IsParaSuper (ball (0 : E d) 2) Q (Ioc 0 1) (fun p ↦ 1 - p.2 / 2) := by
  sorry

end BernoulliComparison
