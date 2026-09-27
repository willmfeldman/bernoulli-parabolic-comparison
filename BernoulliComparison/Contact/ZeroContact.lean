/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.FirstContact
public import BernoulliComparison.Contact.BumpPositivity
public import BernoulliComparison.Heat.Dirichlet

/-!
# Contact values vanish

At a first contact point `p⋆`, `u₁(p⋆) = v₁(p⋆) = 0`.

Proof: if `m = u₁(p⋆) = v₁(p⋆) > 0`, then on a small cylinder `C` below `p⋆` both
functions are `≥ m/2`, so `C ⊆ E₁` and `u₁ ≤ v₁` on `C`, strictly below `t⋆`. The caloric
replacement `h` of `u₁` on `Ω = B_ρ(x⋆) × (t₁, t⋆)`, given by the classical solvability of the
heat Dirichlet problem on a ball cylinder (`Heat.caloric_dirichlet_ball`), satisfies `u₁ ≤ h`
(`Heat.domain_comparison_sub` via `Heat.comparison_caloric_sub`), and `h + σP ≤ v₁` with the
caloric paraboloid `P` (`κ = 1/2`) and `σ = min (v₁ - u₁)` on the bottom face
(`Heat.comparison_caloric_super`). At `p⋆`: `m ≥ m + σ/4`.

The time step is `τ = ρ² / (8(d + 1))` instead of `ρ² / (8d)`, so that no
`d ≥ 1` hypothesis is needed; the only property used is `2dτ/ρ² ≤ 1/4`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

namespace Contact

open Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset} {p : E d × ℝ}

/-- Zero contact values: at a first contact point `p⋆`, `u₁(p⋆) = v₁(p⋆) = 0`. -/
theorem zero_contact (h : P.IsFirstContact p) : P.u₁ p = 0 ∧ P.v₁ p = 0 := by
  have hu0 := h.u₁_nonneg
  suffices hm0 : P.u₁ p = 0 from ⟨hm0, h.u₁_eq_v₁.symm.trans hm0⟩
  by_contra hne
  have hm : 0 < P.u₁ p := lt_of_le_of_ne hu0 (Ne.symm hne)
  set m := P.u₁ p with hmdef
  have hvm : P.v₁ p = m := h.u₁_eq_v₁.symm
  have hpD := h.mem_D₁
  have hr₀ := P.r₀_pos
  /- Step 1: a cylinder `C` below `p⋆` where `u₁, v₁ > m/2`. -/
  have hev : ∀ᶠ q in 𝓝[P.D₁] p, m / 2 < P.u₁ q ∧ m / 2 < P.v₁ q :=
    ((P.continuousOn_u₁ p hpD).eventually (lt_mem_nhds (by linarith))).and
      ((P.continuousOn_v₁ p hpD).eventually (lt_mem_nhds (by rw [hvm]; linarith)))
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set ρ := min (min (ε / 2) P.r₀) 1 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have : ρ ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hρr : ρ ≤ P.r₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith
  set C := closedBall p.1 ρ ×ˢ Icc (p.2 - ρ ^ 2) p.2 with hCdef
  have hCroom : C ⊆ P.U₁ ×ˢ Ioc (2 * P.μ) T := by
    rintro q ⟨hq1, hq2⟩
    rw [mem_closedBall, dist_eq_norm] at hq1
    exact h.mem_room (by linarith) (by linarith [hq2.1]) hq2.2
  have hCD : C ⊆ P.D₁ := hCroom.trans P.prod_Ioc_subset_D₁
  have hCpos : ∀ q ∈ C, m / 2 < P.u₁ q ∧ m / 2 < P.v₁ q := by
    intro q hq
    refine hεball ⟨?_, hCD hq⟩
    obtain ⟨hq1, hq2⟩ := hq
    rw [mem_closedBall] at hq1
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨by linarith, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hq2.1, hq2.2]
  have hCE : ∀ q ∈ C, q ∈ P.E₁ := fun q hq ↦
    P.mem_E₁_of_u₁_pos (hCD hq) (by linarith [(hCpos q hq).1])
  have hClt : ∀ q ∈ C, q.2 < p.2 → P.u₁ q < P.v₁ q := fun q hq hqt ↦
    h.lt_of_lt q (hCE q hq) hqt
  have hCle : ∀ q ∈ C, P.u₁ q ≤ P.v₁ q := by
    intro q hq
    rcases hq.2.2.lt_or_eq with hlt | heq
    · exact (hClt q hq hlt).le
    · exact h.le_of_eq q (hCE q hq) heq
  /- Step 2: the time step and the bottom gap `σ`. -/
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set τ := ρ ^ 2 / (8 * ((d : ℝ) + 1)) with hτdef
  have hτ : 0 < τ := by positivity
  have hτρ : τ ≤ ρ ^ 2 := by
    rw [hτdef, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ρ]
  set t₁ := p.2 - τ with ht₁def
  have ht₁ : t₁ < p.2 := by linarith
  set Box := closedBall p.1 ρ ×ˢ Icc t₁ p.2 with hBoxdef
  have hBoxC : Box ⊆ C := fun q hq ↦ ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩
  have hbotC : ∀ y ∈ closedBall p.1 ρ, (y, t₁) ∈ C := fun y hy ↦
    hBoxC ⟨hy, le_rfl, ht₁.le⟩
  have hfc : ContinuousOn (fun y : E d ↦ P.v₁ (y, t₁) - P.u₁ (y, t₁)) (closedBall p.1 ρ) := by
    have hg : ContinuousOn (fun y : E d ↦ (y, t₁)) (closedBall p.1 ρ) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hmaps : MapsTo (fun y : E d ↦ (y, t₁)) (closedBall p.1 ρ) P.D₁ :=
      fun y hy ↦ hCD (hbotC y hy)
    exact (P.continuousOn_v₁.comp hg hmaps).sub (P.continuousOn_u₁.comp hg hmaps)
  obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall p.1 ρ).exists_isMinOn
    (nonempty_closedBall.mpr hρ.le) hfc
  set σ := P.v₁ (y₀, t₁) - P.u₁ (y₀, t₁) with hσdef
  have hσ : 0 < σ := sub_pos.2 (hClt _ (hbotC y₀ hy₀) ht₁)
  have hσle : ∀ y ∈ closedBall p.1 ρ, σ ≤ P.v₁ (y, t₁) - P.u₁ (y, t₁) :=
    fun y hy ↦ isMinOn_iff.mp hmin y hy
  /- Step 3: the caloric replacement `H` of `u₁` (`Heat.caloric_dirichlet_ball`) lies above `u₁`. -/
  have hclA : closure (ball p.1 ρ) = closedBall p.1 ρ := closure_ball p.1 hρ.ne'
  have hpb : parBdry (ball p.1 ρ) t₁ p.2 ⊆ Box := by
    rintro q (⟨hq1, hq2⟩ | ⟨hq1, hq2⟩)
    · rw [hclA] at hq1
      rw [mem_singleton_iff] at hq2
      exact ⟨hq1, by rw [hq2], by rw [hq2]; exact ht₁.le⟩
    · exact ⟨hclA ▸ frontier_subset_closure hq1, hq2⟩
  have hBoxD : Box ⊆ P.D₁ := hBoxC.trans hCD
  obtain ⟨H, hHc, hHs, hHcal, hHeq⟩ := Heat.caloric_dirichlet_ball p.1 hρ ht₁
    (P.continuousOn_u₁.mono (hpb.trans hBoxD))
  set Ω := ball p.1 ρ ×ˢ Ioo t₁ p.2 with hΩdef
  have hΩBox : Ω ⊆ Box := prod_mono ball_subset_closedBall Ioo_subset_Icc_self
  have hΩo : IsOpen Ω := isOpen_ball.prod isOpen_Ioo
  have hsubΩ : IsCaloricSub Ω P.u₁ :=
    (P.isSubcal_one.restrict (hΩBox.trans (hBoxC.trans hCroom)) hΩo.isParOpen).isCaloricSub
  have hBox' : closure (ball p.1 ρ) ×ˢ Icc t₁ p.2 = Box := by rw [hclA]
  have hpBox : p ∈ Box := ⟨mem_closedBall_self hρ.le, ht₁.le, le_rfl⟩
  have huH := Heat.comparison_caloric_sub (W := P.u₁) (b := H) isOpen_ball isBounded_ball ht₁
    hsubΩ (by rw [hBox']; exact P.continuousOn_u₁.mono hBoxD) (by rw [hBox']; exact hHc) hHs
    (fun q hq ↦ by rw [hHcal q hq, sub_self])
    (fun q hq ↦ (hHeq hq).ge)
  have hmH : m ≤ H p := huH p (hBox'.symm ▸ hpBox)
  /- Step 4: `H + σ Pb ≤ v₁` with the caloric paraboloid `Pb` (`κ = 1/2`). -/
  set Pb := Barriers.paraboloid p.1 t₁ ρ (1 / 2) with hPbdef
  have hPbs : ContDiff ℝ ∞ Pb := Barriers.contDiff_paraboloid _ _ _ _
  set b : E d × ℝ → ℝ := fun q ↦ H q + (σ * Pb q + 0) with hbdef
  have hΩpos : Ω ⊆ posSetP P.v₁ (P.U₁ ×ˢ Ioc (2 * P.μ) T) := fun q hq ↦
    ⟨hCroom (hBoxC (hΩBox hq)), by linarith [(hCpos q (hBoxC (hΩBox hq))).2]⟩
  have hsupΩ : IsCaloricSuper Ω P.v₁ :=
    (P.isSupercal_one.restrict hΩpos hΩo.isParOpen).isCaloricSuper
  have hbv := Heat.comparison_caloric_super (v := P.v₁) (b := b) isOpen_ball isBounded_ball ht₁
    hsupΩ (by rw [hBox']; exact P.continuousOn_v₁.mono hBoxD)
    (by
      rw [hBox']
      exact hHc.add ((continuousOn_const.mul hPbs.continuous.continuousOn).add
        continuousOn_const))
    (hHs.add ((contDiffOn_const.mul hPbs.contDiffOn).add contDiffOn_const))
    (fun q hq ↦ by
      rw [hbdef, dₜ_sub_lapₓ_add_mul_add_of_contDiffOn hΩo hq hHs hPbs.contDiffOn,
        hHcal q hq, Barriers.dₜ_sub_lapₓ_paraboloid]
      simp)
    (fun q hq ↦ by
      have hHq : H q = P.u₁ q := hHeq hq
      have hqBox := hpb hq
      simp only [hbdef, hHq, add_zero]
      rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
      · rw [hclA] at hq1
        rw [mem_singleton_iff] at hq2
        have hP : Pb q ≤ 1 / 2 := Barriers.paraboloid_le hq2.ge
        have hgap := hσle q.1 hq1
        have hq' : (q.1, t₁) = q := Prod.ext rfl hq2.symm
        rw [hq'] at hgap
        nlinarith
      · rw [frontier_ball p.1 hρ.ne', mem_sphere, dist_eq_norm] at hq1
        have hP : Pb q ≤ 1 / 2 - 1 := Barriers.paraboloid_le_sub_one hρ hq2.1 hq1.ge
        have := hCle q (hBoxC hqBox)
        nlinarith)
  have hbp := hbv p (hBox'.symm ▸ hpBox)
  have hPbp : Pb p = 1 / 2 - 2 * d * (p.2 - t₁) / ρ ^ 2 := Barriers.paraboloid_center p.2
  have hq : 2 * (d : ℝ) * (p.2 - t₁) / ρ ^ 2 ≤ 1 / 4 := by
    rw [ht₁def, sub_sub_cancel, hτdef, div_le_iff₀ (by positivity), mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ρ]
  simp only [hbdef, add_zero] at hbp
  rw [hvm, hPbp] at hbp
  nlinarith

end Contact

end BernoulliComparison
