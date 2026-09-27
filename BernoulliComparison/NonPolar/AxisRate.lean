/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.NonPolar.Collinearity
public import BernoulliComparison.Barriers.Slope

/-!
# The axis rate ceiling

If `ν²ₓ ≠ 0`, then `liminf_{k ↓ 0} v₁(x⋆ + k e, t⋆)/k ≤ c₂` for every unit vector `e`
(`NonPolar.axis_rate`). It is stated in the contrapositive form: for all `δ' > 0` and `k₀ > 0`
there is `k ∈ (0, k₀]` with `v₁(x⋆ + k e, t⋆) < (c₂ + δ') k`.

The bound holds for every unit vector `e`, not only for `e = -ν²ₓ/|ν²ₓ|`, because depth transfer
(`NonPolar.depth_transfer`) holds for every unit `e` and nothing else uses `e`. In Kim (2003) the
rate of the supersolution is transferred only along the common direction of the spatial normals,
which requires their collinearity; here collinearity is not needed. The proof uses no half ball
or chord: `Barriers.slope_super` is applied with centre `z₀ = x⋆` and a linear radius
`R(t) = R₀ - M (t_q - t)` lying below the slice radius `R_b(t)` of `B̄_μ(p̂)` on a short window,
which is checked by squaring (`M = (μ + 1)/(μ |ν²ₓ|)`, window length `τ ≤ 1/(1 + M²)`), so no
concavity is needed.

Proof: suppose `v₁(x⋆ + k e, t⋆) ≥ β k`, `β = c₂ + δ'`, for `k ∈ (0, k₀]`. Near `q₂` the depth
`κ = R_b(t) - |x - x⋆|` is small (`κ(q₂) = 0`). On `N = B̄_ς(x_q) × [t_q - τ, t_q]`, where
`R(t) - |x - x⋆| > 0` we get `z ∈ B̄_μ(p̂)` and `κ(z) ≥ R(t) - |x - x⋆|`, so
`v₀(z) ≥ v₁(x⋆ + κ e, t⋆) ≥ β κ(z) ≥ β (R(t) - |x - x⋆|)`. `Barriers.slope_super` (with
`TSuper(O₀, v₀, c₂)`) gives `v₀(q₂) > 0`, contradicting `v₀(q₂) = 0`.

## Reference

* I. C. Kim, *A free boundary problem arising in flame propagation*, J. Differential Equations
  191 (2003), 470–489.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace NonPolar

open Contact Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset}

variable (C : ContactData P)

/-- `κ(q₂) = 0`: `q₂` lies on the sphere, at spatial distance `R_b(t_q) = μ|ν²ₓ|` from `x⋆`. -/
theorem depth_q₂ : C.depth C.q₂ = 0 := by
  have hμ := P.μ_pos
  have hunit := C.ν₂_unit
  have h1 : C.q₂.1 - C.xstar = P.μ • C.ν₂.1 := by rw [C.q₂_fst, add_sub_cancel_left]
  have h2 : C.q₂.2 - C.phat.2 = P.μ * C.ν₂.2 := by rw [C.q₂_snd, C.phat_snd]; ring
  rw [ContactData.depth, ContactData.slice, h1, h2, norm_smul, Real.norm_of_nonneg hμ.le]
  have : P.μ ^ 2 - (P.μ * C.ν₂.2) ^ 2 = (P.μ * ‖C.ν₂.1‖) ^ 2 := by
    linear_combination (-P.μ ^ 2) * hunit
  rw [this, Real.sqrt_sq (by positivity), sub_self]

/-- The axis rate ceiling, in contrapositive form, for every unit vector `e` (see the module
docstring). If `ν²ₓ ≠ 0`, then for all `δ' > 0`, `k₀ > 0` there is `k ∈ (0, k₀]` with
`v₁(x⋆ + k e, t⋆) < (c₂ + δ') k`. -/
theorem axis_rate (h₂ : C.ν₂.1 ≠ 0) {e : E d} (he : ‖e‖ = 1) {δ' : ℝ} (hδ' : 0 < δ')
    {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∃ k ∈ Ioc 0 k₀, P.v₁ (C.xstar + k • e, C.tstar) < (C.c₂ + δ') * k := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hμ := P.μ_pos
  have hc₂ := C.c₂_pos
  set β := C.c₂ + δ' with hβ
  have hβpos : 0 < β := by linarith
  set k₁ := min k₀ P.r₀ with hk₁
  have hk₁pos : 0 < k₁ := lt_min hk₀ P.r₀_pos
  set a := ‖C.ν₂.1‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 h₂
  set b := C.ν₂.2 with hb
  have hunit : a ^ 2 + b ^ 2 = 1 := C.ν₂_unit
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg (b + 1)]
  set R₀ := ‖C.q₂.1 - C.xstar‖ with hR₀
  have hR₀eq : R₀ = P.μ * a := by
    rw [hR₀, C.q₂_fst, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hμ.le]
  have hR₀pos : 0 < R₀ := by rw [hR₀eq]; positivity
  have htq : C.q₂.2 - C.phat.2 = P.μ * b := by rw [C.q₂_snd, C.phat_snd]; ring
  set M := (P.μ + 1) / (P.μ * a) with hM
  have hMa : P.μ * a * M = P.μ + 1 := by rw [hM]; field_simp
  -- a neighbourhood of `q₂`
  have hq₂O := C.q₂_mem_O₀
  have hopen : IsOpen ((C.Wstar ∩ P.U₀) ×ˢ Ioi (0 : ℝ)) :=
    ((isOpen_ball).inter P.isOpen_U₀).prod isOpen_Ioi
  have hev : ∀ᶠ q in 𝓝 C.q₂, q ∈ (C.Wstar ∩ P.U₀) ×ˢ Ioi (0 : ℝ) ∧ C.depth q < k₁ := by
    refine Filter.Eventually.and (hopen.mem_nhds ⟨hq₂O.1, hq₂O.2.1⟩) ?_
    have := C.continuous_depth.tendsto C.q₂
    rw [depth_q₂] at this
    exact this.eventually (gt_mem_nhds hk₁pos)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set ς := r / 2 with hς
  set τ := min (r / 2) (1 / (1 + M ^ 2)) with hτ
  have hςpos : 0 < ς := by positivity
  have hτpos : 0 < τ := lt_min (by positivity) (by positivity)
  have hτM : τ * (1 + M ^ 2) ≤ 1 := by
    have := min_le_right (r / 2) (1 / (1 + M ^ 2))
    rw [← hτ] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hNdist : ∀ q ∈ closedBall C.q₂.1 ς ×ˢ Icc (C.q₂.2 - τ) C.q₂.2, dist q C.q₂ < r := by
    intro q hq
    rw [Prod.dist_eq, max_lt_iff]
    have h1 := hq.1
    rw [mem_closedBall] at h1
    have h2 := hq.2
    have hτr : τ ≤ r / 2 := min_le_left _ _
    refine ⟨by linarith, ?_⟩
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [h2.1, h2.2]
  have hN : closedBall C.q₂.1 ς ×ˢ Icc (C.q₂.2 - τ) C.q₂.2 ⊆ C.O₀ := by
    intro q hq
    have h := (hball (hNdist q hq)).1
    exact ⟨h.1, h.2, hq.2.2.trans hq₂O.2.2⟩
  have hβc : C.c₂ < β := by linarith
  have key := Barriers.slope_super hc₂ C.touchSuper_zero hR₀pos M hςpos hτpos hN hβc ?_
  · rw [Prod.mk.eta, C.v₀_q₂] at key
    exact lt_irrefl _ key
  intro q hq
  have hqO := hN hq
  have hqD : q ∈ P.D₀ := P.prod_Ioc_subset_D₀ ⟨hqO.1.2, hqO.2⟩
  set k' := R₀ - M * (C.q₂.2 - q.2) - ‖q.1 - C.xstar‖ with hk'
  rcases le_or_gt k' 0 with hk'0 | hk'0
  · rw [max_eq_right hk'0, mul_zero]; exact P.v₀_nonneg hqD
  rw [max_eq_left hk'0.le]
  set s := C.q₂.2 - q.2 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith [hq.2.2]
  have hsτ : s ≤ τ := by rw [hs]; linarith [hq.2.1]
  have hqt : q.2 - C.phat.2 = P.μ * b - s := by rw [hs]; linarith [htq]
  -- the linear radius lies below the slice radius
  have hRpos : 0 ≤ R₀ - M * s := by linarith [norm_nonneg (q.1 - C.xstar)]
  have hsq : (R₀ - M * s) ^ 2 ≤ P.μ ^ 2 - (q.2 - C.phat.2) ^ 2 := by
    rw [hqt, hR₀eq]
    have h1 : s * (1 + M ^ 2) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hsτ (by positivity)).trans hτM
    have h2 : 1 ≤ P.μ + 1 + P.μ * b := by
      have := mul_nonneg hμ.le (by linarith : (0 : ℝ) ≤ b + 1)
      linarith
    have h3 : s ^ 2 * (M ^ 2 + 1) ≤ 2 * s * (P.μ + 1 + P.μ * b) := by
      have e1 := mul_le_mul_of_nonneg_left h1 hs0
      have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * s)
      have e3 : s ^ 2 * (M ^ 2 + 1) = s * (s * (1 + M ^ 2)) := by ring
      linarith
    have e4 : P.μ ^ 2 - (P.μ * b - s) ^ 2 - (P.μ * a - M * s) ^ 2 =
        2 * s * (P.μ + 1 + P.μ * b) - s ^ 2 * (M ^ 2 + 1) := by
      linear_combination (-P.μ ^ 2) * hunit + 2 * s * hMa
    linarith
  have hslice : R₀ - M * s ≤ C.slice q.2 := Real.le_sqrt_of_sq_le hsq
  have hqball : q ∈ stBall C.phat P.μ := by
    rw [mem_stBall, C.phat_fst]
    have hlt : ‖q.1 - C.xstar‖ < R₀ - M * s := by rw [hk'] at hk'0; linarith
    have := pow_le_pow_left₀ (norm_nonneg (q.1 - C.xstar)) hlt.le 2
    linarith
  have hdepth : k' ≤ C.depth q := by
    rw [ContactData.depth, hk']; linarith
  have hdlt : C.depth q < k₁ := (hball (hNdist q hq)).2
  have hdk₀ : C.depth q ≤ k₀ := hdlt.le.trans (min_le_left _ _)
  have hdr₀ : C.depth q < P.r₀ := hdlt.trans_le (min_le_right _ _)
  have h1 := hcon (C.depth q) ⟨hk'0.trans_le hdepth, hdk₀⟩
  have h2 := depth_transfer C hqball he hdr₀
  calc β * k' ≤ β * C.depth q := mul_le_mul_of_nonneg_left hdepth hβpos.le
    _ ≤ P.v₁ (C.xstar + C.depth q • e, C.tstar) := h1
    _ ≤ P.v₀ q := h2

/-- The axis rate ceiling in the direction `e = -ν²ₓ/|ν²ₓ|` of the exterior spatial normal. -/
theorem axis_rate_normal (h₂ : C.ν₂.1 ≠ 0) {δ' : ℝ} (hδ' : 0 < δ') {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∃ k ∈ Ioc 0 k₀,
      P.v₁ (C.xstar + k • -(‖C.ν₂.1‖⁻¹ • C.ν₂.1), C.tstar) < (C.c₂ + δ') * k := by
  refine axis_rate C h₂ ?_ hδ' hk₀
  rw [norm_neg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h₂)]

end NonPolar

end BernoulliComparison
