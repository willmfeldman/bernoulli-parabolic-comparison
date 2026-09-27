/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Heat.Domain

/-!
# Caloric comparison on cylinders

For `Ω = A × (T₀, T₁)` with `A` open and bounded, `frontier Ω ∩ {t < T₁} ⊆ parBdry A T₀ T₁`,
so the domain comparison of `Heat/Domain.lean` gives comparison of sub/supercaloric functions with
barriers which are `C^∞` only in the open cylinder `A × (T₀, T₁)` and continuous on
`closure A × [T₀, T₁]` (`comparison_caloric_sub`, `comparison_caloric_super`). Comparison with a
barrier smooth near the closed cylinder is a special case.

We also record `IsCaloricSub.mono_of_isOpen` (restriction to open subsets), so that a function
subcaloric on any `O ⊇ A × (T₀, T₁)` qualifies.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-- The sub-caloric property restricts to open subsets. -/
theorem IsCaloricSub.mono_of_isOpen {O O' : Set (E d × ℝ)} {u : E d × ℝ → ℝ}
    (h : IsCaloricSub O u) (hO' : IsOpen O') (hO'O : O' ⊆ O) : IsCaloricSub O' u :=
  h.mono hO'O fun p hp ↦ by
    obtain ⟨ρ, hρ, hsub⟩ := exists_parCyl_of_eventually (hO'.mem_nhds hp)
    exact ⟨ρ, hρ, fun q hq ↦ hsub q hq.2⟩

/-- The super-caloric property restricts to open subsets. -/
theorem IsCaloricSuper.mono_of_isOpen {O O' : Set (E d × ℝ)} {u : E d × ℝ → ℝ}
    (h : IsCaloricSuper O u) (hO' : IsOpen O') (hO'O : O' ⊆ O) : IsCaloricSuper O' u :=
  h.mono hO'O fun p hp ↦ by
    obtain ⟨ρ, hρ, hsub⟩ := exists_parCyl_of_eventually (hO'.mem_nhds hp)
    exact ⟨ρ, hρ, fun q hq ↦ hsub q hq.2⟩

namespace Heat

variable {A : Set (E d)} {T₀ T₁ : ℝ}

theorem closure_prod_Ioo (hT : T₀ < T₁) :
    closure (A ×ˢ Ioo T₀ T₁) = closure A ×ˢ Icc T₀ T₁ := by
  rw [closure_prod_eq, closure_Ioo hT.ne]

/-- The boundary of a cylinder below its top lies in the parabolic boundary:
`frontier (A × (T₀, T₁)) ∩ {t < T₁} ⊆ parBdry A T₀ T₁`. -/
theorem mem_parBdry_of_mem_frontier (hT : T₀ < T₁) {p : E d × ℝ}
    (hp : p ∈ frontier (A ×ˢ Ioo T₀ T₁)) (hpT : p.2 < T₁) : p ∈ parBdry A T₀ T₁ := by
  rw [frontier_prod_eq, frontier_Ioo hT, closure_Ioo hT.ne] at hp
  rcases hp with ⟨h1, h2⟩ | h
  · rcases h2 with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd (h2 ▸ hpT : T₁ < T₁) (lt_irrefl _)
  · exact Or.inr h

theorem isBounded_prod_Ioo (hAb : Bornology.IsBounded A) :
    Bornology.IsBounded (A ×ˢ Ioo T₀ T₁) :=
  hAb.prod (Metric.isBounded_Ioo T₀ T₁)

variable {b : E d × ℝ → ℝ}

/-- **Comparison for subcaloric functions on a cylinder.** Let `A` be open and bounded,
`T₀ < T₁`, `W` continuous on `closure A × [T₀, T₁]` and subcaloric in `A × (T₀, T₁)`, and `b`
continuous on `closure A × [T₀, T₁]`, `C^∞` on `A × (T₀, T₁)` with `∂ₜb - Δb ≥ 0` there. If `W ≤ b`
on the parabolic boundary, then `W ≤ b` on `closure A × [T₀, T₁]`. -/
theorem comparison_caloric_sub {W : E d × ℝ → ℝ} (hA : IsOpen A) (hAb : Bornology.IsBounded A)
    (hT : T₀ < T₁) (hW : IsCaloricSub (A ×ˢ Ioo T₀ T₁) W)
    (hWc : ContinuousOn W (closure A ×ˢ Icc T₀ T₁))
    (hbc : ContinuousOn b (closure A ×ˢ Icc T₀ T₁)) (hb : ContDiffOn ℝ ∞ b (A ×ˢ Ioo T₀ T₁))
    (hheat : ∀ p ∈ A ×ˢ Ioo T₀ T₁, 0 ≤ dₜ b p - lapₓ b p)
    (hbdry : ∀ p ∈ parBdry A T₀ T₁, W p ≤ b p) :
    ∀ p ∈ closure A ×ˢ Icc T₀ T₁, W p ≤ b p := by
  rw [← closure_prod_Ioo hT] at hWc hbc ⊢
  exact domain_comparison_sub (hA.prod isOpen_Ioo) (isBounded_prod_Ioo hAb)
    (fun p hp ↦ hp.2.2) hW hWc hbc hb hheat
    fun p hp hpT ↦ hbdry p (mem_parBdry_of_mem_frontier hT hp hpT)

/-- **Comparison for supercaloric functions on a cylinder.** Let `A` be open and bounded,
`T₀ < T₁`, `v` continuous on `closure A × [T₀, T₁]` and supercaloric in `A × (T₀, T₁)`, and `b`
continuous on `closure A × [T₀, T₁]`, `C^∞` on `A × (T₀, T₁)` with `∂ₜb - Δb ≤ 0` there. If `b ≤ v`
on the parabolic boundary, then `b ≤ v` on `closure A × [T₀, T₁]`. -/
theorem comparison_caloric_super {v : E d × ℝ → ℝ} (hA : IsOpen A)
    (hAb : Bornology.IsBounded A) (hT : T₀ < T₁) (hv : IsCaloricSuper (A ×ˢ Ioo T₀ T₁) v)
    (hvc : ContinuousOn v (closure A ×ˢ Icc T₀ T₁))
    (hbc : ContinuousOn b (closure A ×ˢ Icc T₀ T₁)) (hb : ContDiffOn ℝ ∞ b (A ×ˢ Ioo T₀ T₁))
    (hheat : ∀ p ∈ A ×ˢ Ioo T₀ T₁, dₜ b p - lapₓ b p ≤ 0)
    (hbdry : ∀ p ∈ parBdry A T₀ T₁, b p ≤ v p) :
    ∀ p ∈ closure A ×ˢ Icc T₀ T₁, b p ≤ v p := by
  rw [← closure_prod_Ioo hT] at hvc hbc ⊢
  exact domain_comparison_super (hA.prod isOpen_Ioo) (isBounded_prod_Ioo hAb)
    (fun p hp ↦ hp.2.2) hv hvc hbc hb hheat
    fun p hp hpT ↦ hbdry p (mem_parBdry_of_mem_frontier hT hp hpT)

end Heat

end BernoulliComparison
