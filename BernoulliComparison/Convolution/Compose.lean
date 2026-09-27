/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Convolution.Basic

/-!
# Composition of convolutions

For compact nonempty kernels `K`, `K'`, sets `D₁`, `D₀`, `D` with
`D₁ + K' ⊆ D₀`, `D₀ + K ⊆ D`, `D` compact and `w` continuous on `D`: on `D₁`,
`(w^K)^{K'} = w^{K ⊕ K'}` and `(w_K)_{K'} = w_{K ⊕ K'}`; and
`D₁ ∩ ((D₀ ∩ (E ⊖ K)) ⊖ K') = D₁ ∩ (E ⊖ (K ⊕ K'))`.
-/

@[expose] public section

open Set Pointwise

namespace BernoulliComparison

variable {d : ℕ}

section

variable {K K' D₀ D : Set (E d × ℝ)} {w : E d × ℝ → ℝ} {p : E d × ℝ}

theorem add_add_mem_of_subset (hp : ∀ k' ∈ K', p + k' ∈ D₀) (hD₀ : ∀ q ∈ D₀, ∀ k ∈ K, q + k ∈ D) :
    ∀ j ∈ K + K', p + j ∈ D := by
  rintro _ ⟨k, hk, k', hk', rfl⟩
  have := hD₀ _ (hp k' hk') k hk
  beta_reduce
  rwa [add_comm k k', ← add_assoc]

/-- Composition of sup-convolutions: `(w^K)^{K'}(p) = w^{K ⊕ K'}(p)` when `p + K' ⊆ D₀` and
`D₀ + K ⊆ D`, with `D` compact and `w` continuous on `D`. -/
theorem supConv_supConv (hK : IsCompact K) (hKne : K.Nonempty) (hK' : IsCompact K')
    (hK'ne : K'.Nonempty) (hD : IsCompact D) (hw : ContinuousOn w D)
    (hD₀ : ∀ q ∈ D₀, ∀ k ∈ K, q + k ∈ D) (hp : ∀ k' ∈ K', p + k' ∈ D₀) :
    supConv K' (supConv K w) p = supConv (K + K') w p := by
  have hj := add_add_mem_of_subset hp hD₀
  have hc : ContinuousOn (supConv K w) D₀ :=
    (uniformContinuousOn_supConv hK hKne hD hw hD₀).continuousOn
  apply le_antisymm
  · refine supConv_le hK'ne fun k' hk' ↦ supConv_le hKne fun k hk ↦ ?_
    have := le_supConv (hK.add hK') hw hj (add_mem_add hk hk')
    rwa [add_comm k k', ← add_assoc] at this
  · refine supConv_le (hKne.add hK'ne) ?_
    rintro _ ⟨k, hk, k', hk', rfl⟩
    calc w (p + (k + k')) = w (p + k' + k) := by rw [add_comm k k', add_assoc]
      _ ≤ supConv K w (p + k') := le_supConv hK hw (hD₀ _ (hp k' hk')) hk
      _ ≤ supConv K' (supConv K w) p := le_supConv hK' hc hp hk'

/-- Composition of inf-convolutions: `(w_K)_{K'}(p) = w_{K ⊕ K'}(p)` under the same hypotheses. -/
theorem infConv_infConv (hK : IsCompact K) (hKne : K.Nonempty) (hK' : IsCompact K')
    (hK'ne : K'.Nonempty) (hD : IsCompact D) (hw : ContinuousOn w D)
    (hD₀ : ∀ q ∈ D₀, ∀ k ∈ K, q + k ∈ D) (hp : ∀ k' ∈ K', p + k' ∈ D₀) :
    infConv K' (infConv K w) p = infConv (K + K') w p := by
  have hj := add_add_mem_of_subset hp hD₀
  have hc : ContinuousOn (infConv K w) D₀ :=
    (uniformContinuousOn_infConv hK hKne hD hw hD₀).continuousOn
  apply le_antisymm
  · refine le_infConv (hKne.add hK'ne) ?_
    rintro _ ⟨k, hk, k', hk', rfl⟩
    calc infConv K' (infConv K w) p ≤ infConv K w (p + k') := infConv_le hK' hc hp hk'
      _ ≤ w (p + k' + k) := infConv_le hK hw (hD₀ _ (hp k' hk')) hk
      _ = w (p + (k + k')) := by rw [add_comm k k', add_assoc]
  · refine le_infConv hK'ne fun k' hk' ↦ le_infConv hKne fun k hk ↦ ?_
    have := infConv_le (hK.add hK') hw hj (add_mem_add hk hk')
    rwa [add_comm k k', ← add_assoc] at this

end

/-- Composition of convolved sets: if `D₁ + K' ⊆ D₀` then
`(E^K on D₀)^{K'} on D₁ = E^{K ⊕ K'} on D₁`. -/
theorem setConv_setConv {K K' D₀ D₁ Eset : Set (E d × ℝ)}
    (hD₁ : ∀ p ∈ D₁, ∀ k' ∈ K', p + k' ∈ D₀) :
    setConv D₁ K' (setConv D₀ K Eset) = setConv D₁ (K + K') Eset := by
  ext p
  simp only [mem_setConv]
  constructor
  · rintro ⟨hp, k', hk', -, k, hk, hE⟩
    refine ⟨hp, k + k', add_mem_add hk hk', ?_⟩
    rwa [add_comm k k', ← add_assoc]
  · rintro ⟨hp, _, ⟨k, hk, k', hk', rfl⟩, hE⟩
    refine ⟨hp, k', hk', hD₁ p hp k' hk', k, hk, ?_⟩
    beta_reduce at hE
    rwa [add_comm k k', ← add_assoc] at hE

end BernoulliComparison
