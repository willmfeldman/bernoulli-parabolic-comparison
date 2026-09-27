/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Main.Core
public import BernoulliComparison.Main.DimZero

/-!
# Proof of the headline comparison principle

* `Main.para_relaxed_comparison_of_core`: for `d ≥ 1`, the core no-crossing statement
  `Main.core_no_crossing` implies the comparison principle. The margin and the δ-scaling
  `(û, v̂) = ((1 + δ) u, (1 - δ) v)` are packaged in `Crossing.Params.nonempty`. Off the
  interior region `D_{ρ₀} = {(x, t) | B̄_{ρ₀}(x) ⊆ U, ρ₀ ≤ t ≤ T}` the margin gives `u + θ ≤ v`;
  on `D_{ρ₀}` one has the chain `u ≤ û ≤ u₁ < v₁ ≤ v̂ ≤ v` for the convolved pair `(u₁, v₁)`.
  Since the kernel `K` contains `0`, `D_{ρ₀} ⊆ D₁` reaches up to `t = T`, so the conclusion is
  strict also on the top slice.
* `Main.para_relaxed_comparison`: the case split `d = 0` (`para_relaxed_comparison_dim_zero`),
  `U = ∅`, and `d ≥ 1` (`para_relaxed_comparison_of_core`). The headline
  `BernoulliComparison.para_relaxed_comparison` (`Statements/Main.lean`) is proved by this term.
-/

@[expose] public section

open Set Filter Topology

namespace BernoulliComparison

namespace Main

open Crossing

variable {d : ℕ}

/-- The comparison principle for `d ≥ 1`, deduced from the core no-crossing statement
`core_no_crossing`. Same hypotheses and conclusion as `para_relaxed_comparison`, plus `1 ≤ d`. -/
theorem para_relaxed_comparison_of_core (hd : 1 ≤ d) {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T) := by
  obtain ⟨P⟩ := Params.nonempty hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec
  let P' : Config U Q T u v Eset := P
  rintro p ⟨hpE, hpD⟩
  by_cases hpρ : p ∈ interiorRegion U T P'.ρ₀
  · -- `u ≤ û ≤ u₁ < v₁ ≤ v̂ ≤ v`
    have hD₁ := P'.interiorRegion_subset_D₁ hpρ
    have hE₁ := P'.inter_subset_E₁ ⟨hpE, hD₁⟩
    have hcore := core_no_crossing hd P' ⟨p, hpρ⟩ p hE₁
    have hsq := P'.delta_scaled.2.1 p hpD
    linarith [P'.uhat_le_u₁ hD₁, P'.v₁_le_vhat hD₁, hsq.1, hsq.2]
  · -- the margin `u + θ ≤ v` off `D_{ρ₀}`
    linarith [P'.margin_uv p hpE hpρ, P'.θ_pos]

/-- The comparison principle for relaxed subsolutions. Case split: `d = 0`
(`para_relaxed_comparison_dim_zero`, which also handles `U = ∅` there); `U = ∅`
(`precOn_of_eq_empty`); otherwise `para_relaxed_comparison_of_core`. The statement is identical to
that of `BernoulliComparison.para_relaxed_comparison`, whose proof is this term. -/
theorem para_relaxed_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
    {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact para_relaxed_comparison_dim_zero hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec
  rcases U.eq_empty_or_nonempty with hU0 | -
  · exact precOn_of_eq_empty hsub hU0
  exact para_relaxed_comparison_of_core hd hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec

end Main

end BernoulliComparison
