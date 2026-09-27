/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.Caloric

/-!
# No instant creation of the relaxed set

If `(u, E)` is a relaxed subsolution, every point `p ∈ E` (with `p.1 ∈ U`, `I ∈ 𝓝[≤] p.2`, `Q`
continuous and positive at `p.1`) is a limit of points of `E` at strictly earlier times.

Proof. Suppose `E ∩ Q_ρ(p) ⊆ {t = t₀}`. Step 1: `u = 0` on `E ∩ Q_ρ(p)`, since
at a point `(z, t₀)` with `u > 0` the points `(z, s)`, `s ↑ t₀`, lie in `{u > 0} ⊆ E`. Step 2: then
`φ(x, t) = t - t₀` crosses `u` from above in `E` at `p`; but `∂ₜφ - Δφ = 1 > 0` and
`|∇φ| = 0 < Q(x₀)`, contradicting the relaxed bridge.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

namespace BernoulliComparison

variable {d : ℕ}

section

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)}
  {p : E d × ℝ}

/-- The operators of the time coordinate `φ(x, t) = t - t₀`. -/
theorem dₜ_time_sub (t₀ : ℝ) (q : E d × ℝ) : dₜ (fun q : E d × ℝ ↦ q.2 - t₀) q = 1 := by
  simp [dₜ]

theorem lapₓ_time_sub (t₀ : ℝ) (q : E d × ℝ) : lapₓ (fun q : E d × ℝ ↦ q.2 - t₀) q = 0 := by
  simp [lapₓ]

theorem gradₓ_time_sub (t₀ : ℝ) (q : E d × ℝ) : gradₓ (fun q : E d × ℝ ↦ q.2 - t₀) q = 0 := by
  simp [gradₓ]

/-- Past points (no instant creation): every point of `E` (over `U × I`) has points
of `E` at strictly earlier times in each of its backward cylinders. -/
theorem IsParaRelaxedSub.past_points (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) (hQ : ContinuousAt Q p.1) (hQpos : 0 < Q p.1)
    (hpS : p ∈ S) {r : ℝ} (hr : 0 < r) :
    ∃ q ∈ S ∩ parCyl p.1 p.2 r, q.2 < p.2 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨ρ, hρ, hρr, hρsub⟩ := exists_closedParCyl_subset_prod hU hpU hpI hr
  have hcylUI : parCyl p.1 p.2 ρ ⊆ U ×ˢ I := parCyl_subset_closedParCyl.trans hρsub
  have hsame : ∀ q ∈ S ∩ parCyl p.1 p.2 ρ, q.2 = p.2 := fun q hq ↦
    le_antisymm (mem_parCyl.1 hq.2).2.2 (hcon q ⟨hq.1, parCyl_mono hρ.le hρr hq.2⟩)
  -- Step 1: `u = 0` on `S ∩ Q_ρ(p)`.
  have hzero : ∀ q ∈ S ∩ parCyl p.1 p.2 ρ, u q = 0 := by
    intro q hq
    have hqUI := hcylUI hq.2
    refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (hsub.2.1 q hqUI)
    have hq2 := hsame q hq
    obtain ⟨hq1, -, -⟩ := mem_parCyl.1 hq.2
    -- points `(q.1, s)` with `s ↑ p.2` are in `{u > 0} ⊆ S`
    have hlim : Tendsto (fun s : ℝ ↦ (q.1, s)) (𝓝[<] p.2) (𝓝[U ×ˢ I] q) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℝ ↦ (q.1, s)) (𝓝 p.2) (𝓝 q) :=
          (continuous_const.prodMk continuous_id).tendsto' p.2 q (Prod.ext rfl hq2.symm)
        exact this.mono_left nhdsWithin_le_nhds
      · have : ∀ᶠ s in 𝓝[<] p.2, s ∈ I :=
          nhdsWithin_mono _ Iio_subset_Iic_self hpI
        exact this.mono fun s hs ↦ ⟨hqUI.1, hs⟩
    have hev := hlim.eventually ((hsub.1 q hqUI).eventually (lt_mem_nhds hpos))
    have hev2 : ∀ᶠ s in 𝓝[<] p.2, (q.1, s) ∈ U ×ˢ I := (tendsto_nhdsWithin_iff.1 hlim).2
    obtain ⟨s, ⟨hs1, hs2⟩, hs3, hs4⟩ :=
      (Filter.Eventually.and (Ioo_mem_nhdsLT (show p.2 - ρ ^ 2 < p.2 by nlinarith) :
        ∀ᶠ s in 𝓝[<] p.2, s ∈ Ioo (p.2 - ρ ^ 2) p.2) (hev.and hev2)).exists
    have hsS : (q.1, s) ∈ S := hsub.2.2.2.2.1 ⟨hs4, hs3⟩
    have := hsame (q.1, s) ⟨hsS, mem_parCyl.2 ⟨hq1, hs1, hs2.le⟩⟩
    simp only at this
    linarith
  -- Step 2: the test function `t - t₀` crosses `u` from above in `S` at `p`.
  have hcross : CrossesFromAbove S u (fun q ↦ q.2 - p.2) p := by
    refine ⟨hpS, ?_, ρ, hρ, fun q hq ↦ ?_⟩
    · rw [hzero p ⟨hpS, self_mem_parCyl hρ⟩]; simp
    · change u q ≤ q.2 - p.2
      rw [hzero q hq, hsame q hq, sub_self]
  have hφ : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ q.2 - p.2) := contDiff_snd.sub contDiff_const
  rcases hsub.touching_alt hU hpU hpI hQ hφ hcross with h | ⟨-, h⟩
  · rw [dₜ_time_sub, lapₓ_time_sub] at h; norm_num at h
  · rw [gradₓ_time_sub, norm_zero] at h; linarith

/-- Past points, Euclidean-ball form: for every `ε > 0` there is `q ∈ E` with
`q.2 < p.2` and `|q - p| < ε` (Euclidean space-time distance). -/
theorem IsParaRelaxedSub.past_points_euclidean (hsub : IsParaRelaxedSub U Q I u S)
    (hU : IsOpen U) (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) (hQ : ContinuousAt Q p.1)
    (hQpos : 0 < Q p.1) (hpS : p ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ S, q.2 < p.2 ∧ ‖q.1 - p.1‖ ^ 2 + (q.2 - p.2) ^ 2 < ε ^ 2 := by
  set r := min (ε / 2) 1 with hrdef
  have hr : 0 < r := lt_min (half_pos hε) one_pos
  obtain ⟨q, ⟨hqS, hq⟩, hlt⟩ := hsub.past_points hU hpU hpI hQ hQpos hpS hr
  obtain ⟨hq1, hq2, hq3⟩ := mem_parCyl.1 hq
  rw [dist_eq_norm] at hq1
  have hr1 : r ≤ ε / 2 := min_le_left _ _
  have hr2 : r ≤ 1 := min_le_right _ _
  refine ⟨q, hqS, hlt, ?_⟩
  have h1 : ‖q.1 - p.1‖ ^ 2 < r ^ 2 := by
    have := norm_nonneg (q.1 - p.1); nlinarith
  have h3 : r ^ 2 ≤ 1 := by nlinarith
  have h2 : (q.2 - p.2) ^ 2 ≤ r ^ 2 := by
    have h4 : (q.2 - p.2) ^ 2 ≤ (r ^ 2) ^ 2 := by nlinarith
    nlinarith
  have h5 : r ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith
  nlinarith

end

end BernoulliComparison
