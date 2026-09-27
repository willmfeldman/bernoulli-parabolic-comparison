import Challenge.Parabolic
import Challenge.Convolution

/-!
# Challenge: sup- and inf-convolution preserve the solution classes

Let `U, U' ⊆ ℝᵈ`, `α < β`, `α' < β'`, and let `K ⊆ ℝᵈ × ℝ` be a compact kernel containing `0`
whose points have spatial part of norm at most `ℓ`. Assume the translation conditions

* `(Ū' × [α', β']) + K ⊆ Ū × [α, β]` and `(U' × (α', β']) + K ⊆ U × (α, β]`,

that `U` is bounded, and that `Q` is `L`-Lipschitz on `Ū`. Then:

* `challenge_supConv`: if `(u, E)` is a relaxed subsolution for `Q` in `U × (α, β]` and `u` is
  continuous on `Ū × [α, β]`, then `(u^K, E^K)` is a relaxed subsolution for `Q - Lℓ` in
  `U' × (α', β']`, where `u^K = supConv K u` and `E^K = (Ū' × [α', β']) ∩ (E - K)`.
* `challenge_infConv`: if `v` is a supersolution for `Q` in `U × (α, β]`, continuous on
  `Ū × [α, β]`, then `v_K = infConv K v` is a supersolution for `Q + Lℓ` in `U' × (α', β']`.

The free-boundary condition degrades by `Lℓ` because translating a barrier by `k ∈ K` moves `Q`
by at most `L‖k.1‖ ≤ Lℓ`.

All hypotheses are stated individually; the library bundles the kernel and translation
conditions into a structure `ConvStep`, which the solution assembles from them. The vocabulary
is restated in `Challenge/Setting.lean`, `Challenge/Parabolic.lean` and
`Challenge/Convolution.lean`, which import `Mathlib` only.
-/

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-- **Sup-convolution preserves relaxed subsolutions**, with `Q` replaced by `Q - Lℓ`. -/
theorem challenge_supConv {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}
    {Q : E d → ℝ} {u : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)} {L : NNReal} {ℓ : ℝ}
    (hu : IsParaRelaxedSub U Q (Ioc α β) u Eset) (hcont : ContinuousOn u (closure U ×ˢ Icc α β))
    (hU : Bornology.IsBounded U) (hαβ : α < β) (hαβ' : α' < β') (hK : IsCompact K)
    (h0K : (0 : E d × ℝ) ∈ K) (hKℓ : ∀ k ∈ K, ‖k.1‖ ≤ ℓ)
    (hclosed : ∀ p ∈ closure U' ×ˢ Icc α' β', ∀ k ∈ K, p + k ∈ closure U ×ˢ Icc α β)
    (hopen : ∀ p ∈ U' ×ˢ Ioc α' β', ∀ k ∈ K, p + k ∈ U ×ˢ Ioc α β)
    (hQ : LipschitzOnWith L Q (closure U)) :
    IsParaRelaxedSub U' (fun x ↦ Q x - L * ℓ) (Ioc α' β') (supConv K u)
      (setConv (closure U' ×ˢ Icc α' β') K Eset) := by
  sorry

/-- **Inf-convolution preserves supersolutions**, with `Q` replaced by `Q + Lℓ`. -/
theorem challenge_infConv {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}
    {Q : E d → ℝ} {v : E d × ℝ → ℝ} {L : NNReal} {ℓ : ℝ}
    (hv : IsParaSuper U Q (Ioc α β) v) (hcont : ContinuousOn v (closure U ×ˢ Icc α β))
    (hU : Bornology.IsBounded U) (hαβ : α < β) (hαβ' : α' < β') (hK : IsCompact K)
    (h0K : (0 : E d × ℝ) ∈ K) (hKℓ : ∀ k ∈ K, ‖k.1‖ ≤ ℓ)
    (hclosed : ∀ p ∈ closure U' ×ˢ Icc α' β', ∀ k ∈ K, p + k ∈ closure U ×ˢ Icc α β)
    (hopen : ∀ p ∈ U' ×ˢ Ioc α' β', ∀ k ∈ K, p + k ∈ U ×ˢ Ioc α β)
    (hQ : LipschitzOnWith L Q (closure U)) :
    IsParaSuper U' (fun x ↦ Q x + L * ℓ) (Ioc α' β') (infConv K v) := by
  sorry

end BernoulliComparison
