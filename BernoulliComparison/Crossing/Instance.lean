/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Crossing.Abstract
public import BernoulliComparison.Crossing.Config
public import BernoulliComparison.Touching.PastPoints

/-!
# Convolved margin, room, and the first crossing of the configuration

* `Config.margin` (convolved margin): `u₁ + θ'/2 ≤ v₁` on `E₁ \ R₁`.
* `Config.room`: for `p ∈ R₁`,
  `B̄_{2r₀}(p.1) × [p.2 - 2r₀, p.2] ⊆ U₁ × (2μ, T]`, and `2λ < r₀`.
* `Config.past_points` (hypothesis (TS) of `first_crossing`): every point of `E₁ ∩ R₁` is a
  limit of points of `E₁` at strictly earlier times (from `IsParaRelaxedSub.past_points`).
* `Config.first_crossing`: if the crossing set
  `S = {p ∈ E₁ | u₁ p ≥ v₁ p}` is nonempty, its minimal time `t⋆ ∈ [ρ₀, T]` exists, `u₁ < v₁` on
  `E₁ ∩ {t < t⋆}`, `u₁ ≤ v₁` on `E₁ ∩ {t = t⋆}`, and the contact set
  `Ξ = {p ∈ E₁ | p.2 = t⋆, u₁ p = v₁ p}` is nonempty, compact and contained in `R₁`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Crossing

namespace Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} (P : Config U Q T u v Eset)

/-- The crossing set `S = {p ∈ E₁ | u₁ p ≥ v₁ p}`. -/
def crossingSet : Set (E d × ℝ) := {p ∈ P.E₁ | P.v₁ p ≤ P.u₁ p}

/-- The contact set `Ξ = {p ∈ E₁ | p.2 = t, u₁ p = v₁ p}` at time `t`. -/
def contactSet (t : ℝ) : Set (E d × ℝ) := {p ∈ P.E₁ | p.2 = t ∧ P.u₁ p = P.v₁ p}

/-- (P3) at kernel translates: `|v̂(p + k) - v̂(p + k')| ≤ θ'/2` for `p ∈ D₁`, `k, k' ∈ K`. -/
theorem abs_vhat_sub_le {p : E d × ℝ} (hp : p ∈ P.D₁) {k k' : E d × ℝ} (hk : k ∈ P.K)
    (hk' : k' ∈ P.K) : |P.vhat (p + k) - P.vhat (p + k')| ≤ P.θ' / 2 := by
  have h := P.P3 (p + k) (P.convStep_one.closedDomain_add p hp k hk) (p + k')
    (P.convStep_one.closedDomain_add p hp k' hk') (by
      have := P.sq_dist_le_of_mem_K hk hk'
      simp only [Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub]
      exact this)
  rw [θ', show P.θ / 2 / 2 = P.θ / 4 by ring]
  exact h

/-- The convolved margin: `u₁ + θ'/2 ≤ v₁` on `E₁ \ R₁`. -/
theorem margin {p : E d × ℝ} (hp : p ∈ P.E₁) (hpR : p ∉ P.R₁) :
    P.u₁ p + P.θ' / 2 ≤ P.v₁ p := by
  obtain ⟨hpD₁, k₀, hk₀, hk₀E⟩ := hp
  have hpK : ∀ k ∈ P.K, p + k ∈ P.D := P.convStep_one.closedDomain_add p hpD₁
  -- no point of `p + K` lies in `D_{ρ₀}`
  have hnot : ∀ k ∈ P.K, p + k ∉ interiorRegion U T P.ρ₀ := by
    rintro k hk ⟨hball, hρ, -⟩
    have ht := P.snd_mem_Icc_of_mem_K hk
    have hk1 := P.norm_fst_le_of_mem_K hk
    refine hpR ⟨(closedBall_subset_closedBall' ?_).trans hball, ?_, hpD₁.2.2⟩
    · rw [Prod.fst_add, dist_comm, dist_eq_norm, add_sub_cancel_left]
      linarith
    · rw [Prod.snd_add] at hρ
      linarith [ht.2]
  obtain ⟨ks, hks, hkseq⟩ := exists_infConv_eq P.isCompact_K ⟨0, P.zero_mem_K⟩
    P.continuousOn_vhat hpK
  have hv₁ : P.v₁ p = P.vhat (p + ks) := hkseq
  rcases lt_or_ge 0 (P.u₁ p) with hpos | hnpos
  · obtain ⟨km, hkm, hkmeq⟩ := exists_supConv_eq P.isCompact_K ⟨0, P.zero_mem_K⟩
      P.continuousOn_uhat hpK
    have hu₁ : P.u₁ p = P.uhat (p + km) := hkmeq
    have hE : p + km ∈ Eset := P.mem_Eset_of_uhat_pos (hpK km hkm) (hu₁ ▸ hpos)
    have h1 := P.margin_hat _ hE (hnot km hkm)
    have h2 := (abs_le.mp (P.abs_vhat_sub_le hpD₁ hkm hks)).2
    rw [hu₁, hv₁]
    linarith
  · have h1 := P.margin_hat _ hk₀E (hnot k₀ hk₀)
    have h0 := P.uhat_nonneg (hpK k₀ hk₀)
    have h2 := (abs_le.mp (P.abs_vhat_sub_le hpD₁ hk₀ hks)).2
    rw [hv₁]
    linarith

/-- Room around points of `R₁`:
`B̄_{2r₀}(x) × [t - 2r₀, t] ⊆ U₁ × (2μ, T]` for `(x, t) ∈ R₁`, and `2λ < r₀`. -/
theorem room {p : E d × ℝ} (hp : p ∈ P.R₁) :
    closedBall p.1 (2 * P.r₀) ×ˢ Icc (p.2 - 2 * P.r₀) p.2 ⊆ P.U₁ ×ˢ Ioc (2 * P.μ) T ∧
      2 * P.lam < P.r₀ := by
  obtain ⟨hball, hρ, hT⟩ := hp
  have hl := P.lam_lt
  have hμ := P.two_μ_lt_ρ₀
  have hlμ := P.μ_lt_lam
  have hl0 := P.lam_pos
  refine ⟨?_, by rw [r₀]; linarith⟩
  rintro ⟨y, s⟩ ⟨hy, hs⟩
  rw [mem_closedBall, r₀] at hy
  refine ⟨(closedBall_subset_closedBall' ?_).trans hball, ?_, hs.2.trans hT⟩
  · linarith
  · rw [r₀] at hs
    linarith [hs.1]

/-- `R₁ ⊆ U₁ × (2μ, T]`. -/
theorem mem_U₁_Ioc_of_mem_R₁ {p : E d × ℝ} (hp : p ∈ P.R₁) :
    p ∈ P.U₁ ×ˢ Ioc (2 * P.μ) T :=
  (P.room hp).1 ⟨mem_closedBall_self (by linarith [P.r₀_pos]),
    by linarith [P.r₀_pos], le_rfl⟩

/-- `Q₁⁻ ≥ (1 + δ)(c - Lλ) > 0` on `Ū`, by (P2). -/
theorem Qsub₁_pos {x : E d} (hx : x ∈ closure U) : 0 < P.Qsub₁ x := by
  have hc := P.c_le x hx
  have h2 := P.P2
  have hδ := P.δ_le_half
  have hδ0 := P.δ_pos
  have hc0 := P.c_pos
  have hL : 8 * (P.L : ℝ) * P.lam ≤ P.c / 2 := by
    rw [lam]; nlinarith
  unfold Qsub₁
  have : 0 < Q x - P.L * P.lam := by linarith
  positivity

/-- Hypothesis (TS) of `first_crossing` for the configuration (from
`IsParaRelaxedSub.past_points`):
every point of `E₁ ∩ R₁` is a limit of points of `E₁` at strictly earlier times. -/
theorem past_points {p : E d × ℝ} (hp : p ∈ P.E₁ ∩ P.R₁) :
    p ∈ closure (P.E₁ ∩ {q : E d × ℝ | q.2 < p.2}) := by
  obtain ⟨hpU, hpI⟩ := P.mem_U₁_Ioc_of_mem_R₁ hp.2
  have hQ : ContinuousAt Q p.1 :=
    P.lipschitzOnWith.continuousOn.continuousAt
      (mem_of_superset (P.isOpen.mem_nhds (P.U₁_subset hpU)) subset_closure)
  have hQ₁ : ContinuousAt P.Qsub₁ p.1 := by
    unfold Qsub₁
    exact continuousAt_const.mul (hQ.sub continuousAt_const)
  have hQpos := P.Qsub₁_pos (subset_closure (P.U₁_subset hpU))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q, hqE, hqt, hq⟩ := P.isParaRelaxedSub_one.past_points_euclidean P.isOpen_U₁ hpU
    (Ioc_mem_nhdsLE_of_mem hpI) hQ₁ hQpos hp.1 hε
  refine ⟨q, ⟨hqE, hqt⟩, ?_⟩
  have h1 : ‖q.1 - p.1‖ ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg (q.2 - p.2)]
  have h2 : (q.2 - p.2) ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg ‖q.1 - p.1‖]
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, norm_sub_rev, Real.dist_eq, abs_sub_comm]
  exact ⟨lt_of_pow_lt_pow_left₀ 2 hε.le h1, abs_lt_of_sq_lt_sq h2 hε.le⟩

/-- First crossing for the configuration. If the crossing set `S = {p ∈ E₁ | u₁ p ≥ v₁ p}` is
nonempty, there is `t⋆ ∈ [ρ₀, T]`, the minimal time of `S` (attained), such that `u₁ < v₁` on
`E₁ ∩ {t < t⋆}`, `u₁ ≤ v₁` on `E₁ ∩ {t = t⋆}`, and the contact set
`Ξ = {p ∈ E₁ | p.2 = t⋆, u₁ p = v₁ p}` is nonempty, compact, and contained in `S ∩ R₁`. -/
theorem first_crossing (hne : P.crossingSet.Nonempty) :
    ∃ tstar : ℝ, P.ρ₀ ≤ tstar ∧ tstar ≤ T ∧
      (∃ p ∈ P.crossingSet, p.2 = tstar) ∧
      (∀ p ∈ P.crossingSet, tstar ≤ p.2) ∧
      (∀ p ∈ P.E₁, p.2 < tstar → P.u₁ p < P.v₁ p) ∧
      (∀ p ∈ P.E₁, p.2 = tstar → P.u₁ p ≤ P.v₁ p) ∧
      (P.contactSet tstar).Nonempty ∧ IsCompact (P.contactSet tstar) ∧
      P.contactSet tstar ⊆ P.crossingSet ∧ P.crossingSet ⊆ P.R₁ := by
  have hgap : ∀ p ∈ P.E₁ \ P.R₁, P.u₁ p < P.v₁ p := fun p hp ↦ by
    have := P.margin hp.1 hp.2
    linarith [P.θ'_pos]
  obtain ⟨p₀, hp₀, hmin, hi, hii, hΞne, hΞc, hΞS, hSR⟩ :=
    Crossing.first_crossing P.isCompact_D₁ P.isClosed_E₁ P.E₁_subset_D₁ P.continuousOn_u₁
      P.continuousOn_v₁ hgap (fun p hp ↦ P.past_points hp) hne
  have hR := hSR hp₀
  exact ⟨p₀.2, hR.2.1, hR.2.2, ⟨p₀, hp₀, rfl⟩, fun p hp ↦ hmin hp, hi, hii, hΞne, hΞc, hΞS,
    hSR⟩

end Config

end Crossing

end BernoulliComparison
