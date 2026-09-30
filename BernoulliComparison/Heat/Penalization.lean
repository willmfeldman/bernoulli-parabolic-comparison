/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Heat.Local

/-!
# The penalization `ε / (T₁ - t)`

The penalization device used in the domain comparison of `Heat/Domain.lean`: for a bounded open
space-time set `Ω ⊆ {t < T₁}` and a function `F` continuous on `closure Ω` with `F ≤ 0` on
`frontier Ω ∩ {t < T₁}`, the penalized function `F - ε / (T₁ - t)` is very negative near the top
time, so if it is somewhere positive on `Ω`, its supremum over `Ω` is a maximum attained at a point
of `Ω` itself (`exists_isMaxOn_penalized`). Conversely, if `F ≤ ε / (T₁ - t)` on `Ω` for every
`ε > 0`, then `F ≤ 0` on `closure Ω` (`nonpos_on_closure_of_penalized`).

We also record the heat operator of the penalization (`dₜ_sub_lapₓ_penalty`): for `t < T₁`,
`(∂ₜ - Δ) (T₁ - t)⁻¹ = (T₁ - t)⁻²`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Laplacian

namespace BernoulliComparison

variable {d : ℕ}

/-- The penalization profile `(T₁ - t)⁻¹`. -/
noncomputable def penalty (T₁ : ℝ) (q : E d × ℝ) : ℝ := (T₁ - q.2)⁻¹

theorem penalty_pos {T₁ : ℝ} {q : E d × ℝ} (hq : q.2 < T₁) : 0 < penalty T₁ q :=
  inv_pos.2 (sub_pos.2 hq)

theorem contDiffOn_penalty (T₁ : ℝ) :
    ContDiffOn ℝ ∞ (penalty (d := d) T₁) {q | q.2 < T₁} :=
  ((contDiff_const.sub contDiff_snd).contDiffOn).inv fun _ hq ↦ (sub_pos.2 hq).ne'

theorem continuousOn_penalty (T₁ : ℝ) :
    ContinuousOn (penalty (d := d) T₁) {q | q.2 < T₁} :=
  (contDiffOn_penalty T₁).continuousOn

theorem isOpen_setOf_snd_lt (T₁ : ℝ) : IsOpen {q : E d × ℝ | q.2 < T₁} :=
  isOpen_lt continuous_snd continuous_const

/-- Heat operator of the penalization: `(∂ₜ - Δ) (T₁ - t)⁻¹ = ((T₁ - t) ^ 2)⁻¹` for `t < T₁`. -/
theorem dₜ_sub_lapₓ_penalty {T₁ : ℝ} {p : E d × ℝ} (hp : p.2 < T₁) :
    dₜ (penalty T₁) p - lapₓ (penalty T₁) p = ((T₁ - p.2) ^ 2)⁻¹ := by
  have hne : T₁ - p.2 ≠ 0 := (sub_pos.2 hp).ne'
  have hd : HasDerivAt (fun s : ℝ ↦ (T₁ - s)⁻¹) (-(-1) / (T₁ - p.2) ^ 2) p.2 :=
    ((hasDerivAt_id p.2).const_sub T₁).inv hne
  have h1 : dₜ (penalty T₁) p = ((T₁ - p.2) ^ 2)⁻¹ := by
    simp only [dₜ, penalty]
    rw [hd.deriv]
    field_simp
  have h2 : lapₓ (penalty T₁) p = 0 := by
    simp only [lapₓ, penalty]
    rw [InnerProductSpace.laplacian_const]
    rfl
  rw [h1, h2, sub_zero]

section Max

variable {Ω : Set (E d × ℝ)} {F : E d × ℝ → ℝ} {T₁ : ℝ}

/-- **Penalized maximum.** Let `Ω ⊆ {t < T₁}`
be bounded, `F` continuous on `closure Ω` with `F ≤ 0` on `frontier Ω ∩ {t < T₁}`. If
`F - ε (T₁ - t)⁻¹` is positive somewhere on `Ω`, it attains its maximum over `Ω` at a point of
`Ω`. -/
theorem exists_isMaxOn_penalized (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩT : ∀ p ∈ Ω, p.2 < T₁)
    (hF : ContinuousOn F (closure Ω)) (hbdry : ∀ p ∈ frontier Ω, p.2 < T₁ → F p ≤ 0)
    {ε : ℝ} (hε : 0 < ε) {q₁ : E d × ℝ} (hq₁ : q₁ ∈ Ω) (hpos : 0 < F q₁ - ε * penalty T₁ q₁) :
    ∃ p ∈ Ω, 0 < F p - ε * penalty T₁ p ∧
      ∀ q ∈ Ω, F q - ε * penalty T₁ q ≤ F p - ε * penalty T₁ p := by
  have hK₀ : IsCompact (closure Ω) := hΩb.isCompact_closure
  obtain ⟨Λ₀, hΛ₀⟩ := hK₀.bddAbove_image hF
  set Λ := max Λ₀ 0 with hΛdef
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hFΛ : ∀ q ∈ closure Ω, F q ≤ Λ := fun q hq ↦
    (hΛ₀ (mem_image_of_mem F hq)).trans (le_max_left _ _)
  set δ := ε / (Λ + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  -- near the top time the penalized function is negative
  have hneg : ∀ q ∈ closure Ω, q.2 < T₁ → T₁ - δ < q.2 → F q - ε * penalty T₁ q < 0 := by
    intro q hq hqT hqδ
    have hpos' : 0 < T₁ - q.2 := sub_pos.2 hqT
    have hlt : ε * penalty T₁ q > Λ + 1 := by
      rw [penalty, ← div_eq_mul_inv, gt_iff_lt, lt_div_iff₀ hpos']
      have : (Λ + 1) * (T₁ - q.2) < (Λ + 1) * δ :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      rwa [hδdef, mul_div_cancel₀ _ (by linarith)] at this
    linarith [hFΛ q hq]
  set K := closure Ω ∩ {q | q.2 ≤ T₁ - δ} with hKdef
  have hK : IsCompact K := hK₀.inter_right (isClosed_le continuous_snd continuous_const)
  have hKT : ∀ q ∈ K, q.2 < T₁ := fun q hq ↦ by linarith [hq.2.out]
  have hfK : ContinuousOn (fun q ↦ F q - ε * penalty T₁ q) K :=
    (hF.mono inter_subset_left).sub
      (continuousOn_const.mul ((continuousOn_penalty T₁).mono fun q hq ↦ hKT q hq))
  have hq₁K : q₁ ∈ K := by
    refine ⟨subset_closure hq₁, ?_⟩
    by_contra h
    exact absurd hpos (not_lt.2 (hneg q₁ (subset_closure hq₁) (hΩT q₁ hq₁)
      (by simpa using h)).le)
  obtain ⟨p, hpK, hpmax⟩ := hK.exists_isMaxOn ⟨q₁, hq₁K⟩ hfK
  have hpq₁ : F q₁ - ε * penalty T₁ q₁ ≤ F p - ε * penalty T₁ p := hpmax hq₁K
  have hppos : 0 < F p - ε * penalty T₁ p := hpos.trans_le hpq₁
  have hpT : p.2 < T₁ := hKT p hpK
  -- the maximum point is not on the frontier, hence in `Ω`
  have hpΩ : p ∈ Ω := by
    have hnf : p ∉ frontier Ω := fun hfr ↦ by
      have h1 := hbdry p hfr hpT
      have h2 := penalty_pos (d := d) hpT
      nlinarith
    have : p ∈ closure Ω \ frontier Ω := ⟨hpK.1, hnf⟩
    rwa [closure_sdiff_frontier, hΩo.interior_eq] at this
  refine ⟨p, hpΩ, hppos, fun q hq ↦ ?_⟩
  by_cases hqK : q.2 ≤ T₁ - δ
  · exact hpmax ⟨subset_closure hq, hqK⟩
  · exact (hneg q (subset_closure hq) (hΩT q hq) (not_le.1 hqK)).le.trans hppos.le

/-- If `F ≤ ε (T₁ - t)⁻¹` on `Ω ⊆ {t < T₁}` for every `ε > 0` and `F` is continuous on
`closure Ω`, then `F ≤ 0` on `closure Ω` (including the top face `closure Ω ∩ {t = T₁}`). -/
theorem nonpos_on_closure_of_penalized (hΩT : ∀ p ∈ Ω, p.2 < T₁)
    (hF : ContinuousOn F (closure Ω))
    (h : ∀ ε > 0, ∀ q ∈ Ω, F q - ε * penalty T₁ q ≤ 0) : ∀ p ∈ closure Ω, F p ≤ 0 := by
  have hΩ : ∀ q ∈ Ω, F q ≤ 0 := by
    intro q hq
    have hpos : 0 < T₁ - q.2 := sub_pos.2 (hΩT q hq)
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have := h (η * (T₁ - q.2)) (mul_pos hη hpos) q hq
    rw [penalty, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one] at this
    linarith
  intro p hp
  exact ContinuousWithinAt.closure_le hp ((hF p hp).mono subset_closure) continuousWithinAt_const
    hΩ

end Max

end BernoulliComparison
