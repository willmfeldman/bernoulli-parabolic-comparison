/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barrier.Structural
public import BernoulliComparison.Barrier.ClosedDomain

/-!
# Barrier toolkit: margin at the parabolic boundary and the δ-scaling gap

The first two reductions of the comparison proof: strict ordering near the parabolic boundary is
upgraded to a uniform margin, and scaling `u` up and `v` down by `1 ± δ` opens a gap in `Q`.

* `interiorRegion U T ρ = D_ρ = {(x, t) | B̄_ρ(x) ⊆ U, ρ ≤ t ≤ T}`.
* `exists_mem_parBdry_dist_le_of_not_mem_interiorRegion`,
  `dist_parBdry_le_of_not_mem_interiorRegion`: a point of
  `D = Ū × [0, T]` outside `D_ρ` is within distance `ρ` of `∂ₚ(U × (0, T])`.
  Distances are for the sup metric of `E d × ℝ`.
* `margin_of_nhdsSet`: strict ordering `u ≺_E v` on a neighbourhood of `∂ₚ` upgrades
  to a uniform margin `u + θ ≤ v` on `E \ D_{ρ₀}`.
* `margin_delta_scaled`: the scaled pair `((1 + δ) u, (1 - δ) v)` keeps half the
  margin, is squeezed between `u` and `v`, and is a relaxed sub / supersolution pair for the
  scaled `Q`'s.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

variable {d : ℕ}

/-- The interior region `D_ρ := {(x, t) | B̄_ρ(x) ⊆ U, ρ ≤ t ≤ T}`. -/
def interiorRegion (U : Set (E d)) (T ρ : ℝ) : Set (E d × ℝ) :=
  {p | closedBall p.1 ρ ⊆ U ∧ ρ ≤ p.2 ∧ p.2 ≤ T}

/-- Decreasing `ρ` enlarges `D_ρ`. -/
theorem interiorRegion_anti {U : Set (E d)} {T ρ ρ' : ℝ} (h : ρ' ≤ ρ) :
    interiorRegion U T ρ ⊆ interiorRegion U T ρ' := fun _ ⟨hb, h1, h2⟩ ↦
  ⟨(closedBall_subset_closedBall h).trans hb, h.trans h1, h2⟩

/-- Boundary layer, pointwise form. If `U` is open and `p ∈ Ū × [0, T] \ D_ρ`, there
is `q ∈ ∂ₚ(U × (0, T])` with `dist p q ≤ ρ` (sup metric). -/
theorem exists_mem_parBdry_dist_le_of_not_mem_interiorRegion {U : Set (E d)} {T ρ : ℝ}
    {p : E d × ℝ} (hU : IsOpen U) (hp : p ∈ closure U ×ˢ Icc 0 T)
    (hpρ : p ∉ interiorRegion U T ρ) : ∃ q ∈ parBdry U 0 T, dist p q ≤ ρ := by
  obtain ⟨hpU, hp0, hpT⟩ := hp
  simp only [interiorRegion, mem_setOf_eq, not_and, not_le] at hpρ
  by_cases hball : closedBall p.1 ρ ⊆ U
  · by_cases ht : ρ ≤ p.2
    · exact absurd hpT (not_le.mpr (hpρ hball ht))
    · -- `t < ρ`: the bottom point `(x, 0)`.
      refine ⟨(p.1, 0), Or.inl ⟨hpU, rfl⟩, ?_⟩
      rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_nonneg hp0]
      exact max_le (hp0.trans (not_le.mp ht).le) (not_le.mp ht).le
  · -- a point of `∂U` within `ρ` of `x`, at the same time `t`.
    have hz : ∃ z ∈ frontier U, dist p.1 z ≤ ρ := by
      by_cases hx : p.1 ∈ U
      · obtain ⟨y, hy, hyU⟩ := not_subset.mp hball
        by_contra hno
        push Not at hno
        have hB : closedBall p.1 ρ ∩ frontier U = ∅ := by
          ext z
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro hzB hzF
          exact absurd (hno z hzF) (not_lt.mpr (by rw [dist_comm]; exact mem_closedBall.mp hzB))
        have hyc : y ∉ closure U := fun hyc ↦
          hB.subset ⟨hy, by rw [hU.frontier_eq]; exact ⟨hyc, hyU⟩⟩
        have hcover : closedBall p.1 ρ ⊆ U ∪ (closure U)ᶜ := by
          intro z hz
          by_cases hzU : z ∈ U
          · exact Or.inl hzU
          · refine Or.inr fun hzc ↦ hB.subset ⟨hz, ?_⟩
            rw [hU.frontier_eq]; exact ⟨hzc, hzU⟩
        obtain ⟨z, -, hzU, hzc⟩ := (convex_closedBall p.1 ρ).isPreconnected U (closure U)ᶜ hU
          isClosed_closure.isOpen_compl hcover
          ⟨p.1, mem_closedBall_self (dist_nonneg.trans (mem_closedBall.mp hy)), hx⟩ ⟨y, hy, hyc⟩
        exact hzc (subset_closure hzU)
      · refine ⟨p.1, ?_, ?_⟩
        · rw [hU.frontier_eq]; exact ⟨hpU, hx⟩
        · rw [dist_self]
          by_contra hρ
          exact hball (by rw [closedBall_eq_empty.mpr (not_le.mp hρ)]; exact empty_subset _)
    obtain ⟨z, hzF, hzd⟩ := hz
    refine ⟨(z, p.2), Or.inr ⟨hzF, hp0, hpT⟩, ?_⟩
    rw [Prod.dist_eq, dist_self]
    exact max_le hzd (dist_nonneg.trans hzd)

/-- Boundary layer. If `U` is open and `p ∈ Ū × [0, T] \ D_ρ` then
`dist(p, ∂ₚ(U × (0, T])) ≤ ρ` (sup metric of `E d × ℝ`). -/
theorem dist_parBdry_le_of_not_mem_interiorRegion {U : Set (E d)} {T ρ : ℝ} {p : E d × ℝ}
    (hU : IsOpen U) (hp : p ∈ closure U ×ˢ Icc 0 T) (hpρ : p ∉ interiorRegion U T ρ) :
    infDist p (parBdry U 0 T) ≤ ρ := by
  obtain ⟨q, hq, hd⟩ := exists_mem_parBdry_dist_le_of_not_mem_interiorRegion hU hp hpρ
  exact (infDist_le_dist_of_mem hq).trans hd

/-- The parabolic boundary `∂ₚ(U × (0, T])` lies in the closed domain `Ū × [0, T]`. -/
theorem parBdry_subset_closedDomain {U : Set (E d)} {T : ℝ} (hT : 0 ≤ T) :
    parBdry U 0 T ⊆ closure U ×ˢ Icc 0 T := by
  rintro p (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
  · exact ⟨hp1, by rw [mem_singleton_iff.mp hp2]; exact ⟨le_rfl, hT⟩⟩
  · exact ⟨frontier_subset_closure hp1, hp2⟩

/-- `∂ₚ(U × (0, T])` is compact for bounded `U`. -/
theorem isCompact_parBdry {U : Set (E d)} {T : ℝ} (hUb : Bornology.IsBounded U) :
    IsCompact (parBdry U 0 T) :=
  (hUb.isCompact_closure.prod isCompact_singleton).union
    ((hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).prod
      isCompact_Icc)

/-- **Margin at the parabolic boundary.** Let `U` be bounded open, `T > 0`, `u, v` continuous on
`D = Ū × [0, T]`, `E ⊆ D` closed, and `u ≺_E v` on a neighbourhood `N` of `∂ₚ(U × (0, T])`. Then
there are `0 < ρ₀ ≤ T` and `θ > 0` with `u + θ ≤ v` on `E \ D_{ρ₀}`. -/
theorem margin_of_nhdsSet {U : Set (E d)} {T : ℝ} {u v : E d × ℝ → ℝ}
    {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hT : 0 < T)
    (hu : ContinuousOn u (closure U ×ˢ Icc 0 T)) (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hE : IsClosed Eset) (hED : Eset ⊆ closure U ×ˢ Icc 0 T)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    ∃ ρ₀ > 0, ρ₀ ≤ T ∧ ∃ θ > 0, ∀ p ∈ Eset, p ∉ interiorRegion U T ρ₀ → u p + θ ≤ v p := by
  obtain ⟨W, hWo, hPW, hWN⟩ := (mem_nhdsSet_iff_exists).mp hN
  obtain ⟨ρ₁, hρ₁, hthick⟩ := (isCompact_parBdry (T := T) hUb).exists_thickening_subset_open hWo hPW
  set ρ₀ := min (ρ₁ / 2) T with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (half_pos hρ₁) hT
  set F := Eset ∩ cthickening ρ₀ (parBdry U 0 T) with hFdef
  have hFD : F ⊆ closure U ×ˢ Icc 0 T := inter_subset_left.trans hED
  have hFc : IsCompact F :=
    (hUb.isCompact_closure.prod isCompact_Icc).of_isClosed_subset
      (hE.inter isClosed_cthickening) hFD
  have hFN : ∀ p ∈ F, u p < v p := by
    rintro p ⟨hpE, hpth⟩
    refine hprec p ⟨hpE, hWN (hthick ?_)⟩
    exact cthickening_subset_thickening' hρ₁ ((min_le_left _ _).trans_lt (half_lt_self hρ₁)) _
      hpth
  -- the uniform margin on the compact `F`
  obtain ⟨θ, hθ, hθF⟩ : ∃ θ > 0, ∀ p ∈ F, u p + θ ≤ v p := by
    rcases F.eq_empty_or_nonempty with hF | hF
    · exact ⟨1, one_pos, by simp [hF]⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hFc.exists_isMinOn hF ((hv.sub hu).mono hFD)
      refine ⟨v p₀ - u p₀, sub_pos.mpr (hFN p₀ hp₀), fun p hp ↦ ?_⟩
      have := hmin hp
      simp only [mem_setOf_eq] at this
      linarith
  refine ⟨ρ₀, hρ₀, min_le_right _ _, θ, hθ, fun p hpE hpρ ↦ hθF p ⟨hpE, ?_⟩⟩
  obtain ⟨q, hq, hd⟩ := exists_mem_parBdry_dist_le_of_not_mem_interiorRegion hU (hED hpE) hpρ
  exact mem_cthickening_of_dist_le p q ρ₀ _ hq hd

/-- **δ-scaling (the gap in `Q`).** Given the margin `u + θ ≤ v` on `E \ D_{ρ₀}`,
nonnegativity of `u, v` on `D = Ū × [0, T]`, a bound `u + v ≤ M` on `D`, and
`0 < δ ≤ 1/2` with `δ (M + 1) ≤ θ / 2`, the pair `û = (1 + δ) u`, `v̂ = (1 - δ) v` satisfies
(a) `û + θ/2 ≤ v̂` on `E \ D_{ρ₀}`; (b) `u ≤ û`, `v̂ ≤ v` on `D`; (c) `(û, E)` is a relaxed
subsolution for `(1 + δ) Q` and `v̂` a supersolution for `(1 - δ) Q` on `U × I`. -/
theorem margin_delta_scaled {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {T ρ₀ θ M δ : ℝ}
    {u v : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)}
    (hsub : IsParaRelaxedSub U Q I u Eset) (hsuper : IsParaSuper U Q I v)
    (hED : Eset ⊆ closure U ×ˢ Icc 0 T)
    (hmargin : ∀ p ∈ Eset, p ∉ interiorRegion U T ρ₀ → u p + θ ≤ v p)
    (hu0 : ∀ p ∈ closure U ×ˢ Icc 0 T, 0 ≤ u p) (hv0 : ∀ p ∈ closure U ×ˢ Icc 0 T, 0 ≤ v p)
    (hM : ∀ p ∈ closure U ×ˢ Icc 0 T, u p + v p ≤ M)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδθ : δ * (M + 1) ≤ θ / 2) :
    (∀ p ∈ Eset, p ∉ interiorRegion U T ρ₀ → (1 + δ) * u p + θ / 2 ≤ (1 - δ) * v p) ∧
    (∀ p ∈ closure U ×ˢ Icc 0 T, u p ≤ (1 + δ) * u p ∧ (1 - δ) * v p ≤ v p) ∧
    IsParaRelaxedSub U ((1 + δ) • Q) I ((1 + δ) • u) Eset ∧
    IsParaSuper U ((1 - δ) • Q) I ((1 - δ) • v) := by
  refine ⟨fun p hpE hpρ ↦ ?_, fun p hp ↦ ?_, hsub.smul (by linarith), hsuper.smul (by linarith)⟩
  · have h1 := hmargin p hpE hpρ
    have h2 := hM p (hED hpE)
    have h3 := hu0 p (hED hpE)
    have h4 := hv0 p (hED hpE)
    nlinarith
  · have h3 := hu0 p hp
    have h4 := hv0 p hp
    constructor <;> nlinarith

/-- The bound `M` of `margin_delta_scaled` exists: `u + v` is bounded above on the compact
`D = Ū × [0, T]` when `U` is bounded. -/
theorem exists_bound_add_closedDomain {U : Set (E d)} {T : ℝ} {u v : E d × ℝ → ℝ}
    (hUb : Bornology.IsBounded U)
    (hu : ContinuousOn u (closure U ×ˢ Icc 0 T)) (hv : ContinuousOn v (closure U ×ˢ Icc 0 T)) :
    ∃ M, ∀ p ∈ closure U ×ˢ Icc 0 T, u p + v p ≤ M := by
  obtain ⟨M, hM⟩ := ((hUb.isCompact_closure.prod isCompact_Icc).bddAbove_image (hu.add hv))
  exact ⟨M, fun p hp ↦ hM ⟨p, hp, rfl⟩⟩

/-- A `δ` as in `margin_delta_scaled` exists for any `θ > 0` and `M`. -/
theorem exists_delta_scaling {θ M : ℝ} (hθ : 0 < θ) (hM : 0 ≤ M) :
    ∃ δ > 0, δ ≤ 1 / 2 ∧ δ * (M + 1) ≤ θ / 2 := by
  refine ⟨min (1 / 2) (θ / (2 * (M + 1))), lt_min (by norm_num) (by positivity), min_le_left _ _,
    ?_⟩
  calc min (1 / 2) (θ / (2 * (M + 1))) * (M + 1) ≤ θ / (2 * (M + 1)) * (M + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
    _ = θ / 2 := by field_simp

end BernoulliComparison
