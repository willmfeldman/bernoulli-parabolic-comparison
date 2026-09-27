/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.Data
public import Mathlib.Analysis.Normed.Module.Ray

/-!
# Spatial collinearity and depth transfer

Geometry of the doubly non-polar case. Throughout, `C : ContactData P` is contact data at a first
contact point `p⋆ = (x⋆, t⋆)`, with dual centre `p̂ = (x⋆, t̂)`,
`t̂ = t⋆ - μ`, and unit normals `ν¹, ν²` (`Contact/Data.lean`).

## Main definitions

* `ContactData.slice C t = R_b(t) = (μ² - (t - t̂)²)^{1/2}`, the radius of the time-`t` slice of
  `B̄_μ(p̂)`;
* `ContactData.depth C z = κ(z) = R_b(t) - |x - x⋆|`.

## Main statements

* `NonPolar.collinearity`: if `ν¹ₓ ≠ 0` and `ν²ₓ ≠ 0`, then
  `ν¹ₓ/|ν¹ₓ| = -ν²ₓ/|ν²ₓ|`;
* `NonPolar.depth_transfer`: for `z ∈ B̄_μ(p̂)` with `κ(z) < r₀` and every
  unit `e`, `v₁(x⋆ + κ(z) e, t⋆) ≤ v₀(z)`;
* `NonPolar.axis_mem_E₁`: the points `(x⋆ + k e, t⋆)`, `e = ν¹ₓ/|ν¹ₓ|`, `0 < k ≤ 2μ|ν¹ₓ|`,
  `k ≤ 2r₀`, lie in `E₁` (first step of `NonPolar.no_nonpolar`).

The collinearity of the spatial normals is used in Kim (2003) to transfer the rate of the
supersolution along their common direction. Here the transfer (`NonPolar.depth_transfer`) holds
in every direction, so `NonPolar.collinearity` is proved but not used elsewhere.

## Reference

* I. C. Kim, *A free boundary problem arising in flame propagation*, J. Differential Equations
  191 (2003), 470–489.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Contact

open Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset}

namespace ContactData

variable (C : ContactData P)

/-- `R_b(t) = (μ² - (t - t̂)²)^{1/2}`, the radius of the time-`t` slice of `B̄_μ(p̂)`. -/
noncomputable def slice (t : ℝ) : ℝ := Real.sqrt (P.μ ^ 2 - (t - C.phat.2) ^ 2)

/-- The depth `κ(z) = R_b(t) - |x - x⋆|` of `z = (x, t)` in `B̄_μ(p̂)`. -/
noncomputable def depth (z : E d × ℝ) : ℝ := C.slice z.2 - ‖z.1 - C.xstar‖

theorem phat_fst : C.phat.1 = C.xstar := rfl

theorem phat_snd : C.phat.2 = C.tstar - P.μ := rfl

theorem continuous_depth : Continuous C.depth := by
  unfold depth slice
  fun_prop

theorem slice_sq {t : ℝ} (ht : (t - C.phat.2) ^ 2 ≤ P.μ ^ 2) :
    C.slice t ^ 2 = P.μ ^ 2 - (t - C.phat.2) ^ 2 :=
  Real.sq_sqrt (by linarith)

/-- `|x - x⋆| ≤ R_b(t)` on `B̄_μ(p̂)`. -/
theorem norm_le_slice {z : E d × ℝ} (hz : z ∈ stBall C.phat P.μ) :
    ‖z.1 - C.xstar‖ ≤ C.slice z.2 := by
  rw [mem_stBall] at hz
  exact Real.le_sqrt_of_sq_le (by rw [C.phat_fst] at hz; linarith)

theorem depth_nonneg {z : E d × ℝ} (hz : z ∈ stBall C.phat P.μ) : 0 ≤ C.depth z :=
  sub_nonneg.2 (C.norm_le_slice hz)

/-- `ν¹ₓ` has norm at most `1`. -/
theorem norm_ν₁_fst_le : ‖C.ν₁.1‖ ≤ 1 := by
  have := C.ν₁_unit
  nlinarith [norm_nonneg C.ν₁.1, sq_nonneg C.ν₁.2]

/-- `ν²ₓ` has norm at most `1`. -/
theorem norm_ν₂_fst_le : ‖C.ν₂.1‖ ≤ 1 := by
  have := C.ν₂_unit
  nlinarith [norm_nonneg C.ν₂.1, sq_nonneg C.ν₂.2]

theorem ctr₁_fst : C.ctr₁.1 = C.xstar + P.μ • C.ν₁.1 := by
  rw [C.ctr₁_eq_pstar_add]; rfl

theorem ctr₁_snd : C.ctr₁.2 = C.tstar + P.μ * C.ν₁.2 := by
  rw [C.ctr₁_eq_pstar_add]; rfl

theorem ctr₂_fst : C.ctr₂.1 = C.xstar + P.μ • C.ν₂.1 := by
  rw [C.ctr₂_eq_pstar_add]; rfl

theorem ctr₂_snd : C.ctr₂.2 = C.tstar + P.μ * C.ν₂.2 := by
  rw [C.ctr₂_eq_pstar_add]; rfl

theorem q₂_fst : C.q₂.1 = C.xstar + P.μ • C.ν₂.1 := by
  rw [C.q₂_eq]; rfl

theorem q₂_snd : C.q₂.2 = C.tstar - P.μ + P.μ * C.ν₂.2 := by
  rw [C.q₂_eq]; rfl

theorem q₁_fst : C.q₁.1 = C.xstar + P.μ • C.ν₁.1 := by
  rw [C.q₁_eq]; rfl

theorem q₁_snd : C.q₁.2 = C.tstar - P.μ + P.μ * C.ν₁.2 := by
  rw [C.q₁_eq]; rfl

include C in
theorem μ_lt_r₀ : P.μ < P.r₀ := by
  have := C.room.2; have := P.μ_lt_lam; have := P.μ_pos; linarith

/-- Points `(x, t)` with `|x - x⋆| ≤ 2r₀` and `t⋆ - 2r₀ ≤ t ≤ t⋆` lie in `D₁`. -/
theorem mem_D₁_of_near {q : E d × ℝ} (hx : ‖q.1 - C.xstar‖ ≤ 2 * P.r₀)
    (ht1 : C.tstar - 2 * P.r₀ ≤ q.2) (ht2 : q.2 ≤ C.tstar) : q ∈ P.D₁ :=
  P.prod_Ioc_subset_D₁ (C.mem_room hx ht1 ht2)

end ContactData

end Contact

namespace NonPolar

open Contact Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset}


variable (C : ContactData P)

/-- Spatial collinearity of the normals. If `ν¹ₓ ≠ 0` and `ν²ₓ ≠ 0`, then
`ν¹ₓ/|ν¹ₓ| = -ν²ₓ/|ν²ₓ|`.

Proof: otherwise the spatial balls `B_{μ|νⁱₓ|}(x⋆ + μ νⁱₓ)` (the time-`t⋆` slices of the touching
balls) meet at some `x'`; then `(x', t⋆ - s)` lies in both touching balls for small `s > 0`, hence
in `E₁` (`interior_ball`), contradicting `exterior_past`. So `|ν¹ₓ - ν²ₓ| = |ν¹ₓ| + |ν²ₓ|`, the
equality case of the triangle inequality. -/
theorem collinearity (h₁ : C.ν₁.1 ≠ 0) (h₂ : C.ν₂.1 ≠ 0) :
    ‖C.ν₁.1‖⁻¹ • C.ν₁.1 = -(‖C.ν₂.1‖⁻¹ • C.ν₂.1) := by
  have hμ := P.μ_pos
  set n₁ := C.ν₁.1 with hn₁
  set n₂ := C.ν₂.1 with hn₂
  have hray : ‖n₁‖ • (-n₂) = ‖-n₂‖ • n₁ := by
    refine Eq.symm (norm_add_eq_iff_real.1 ?_)
    by_contra hne
    have hnot : ‖n₁ - n₂‖ < ‖n₁‖ + ‖n₂‖ := by
      have := (norm_add_le n₁ (-n₂)).lt_of_ne hne
      rwa [norm_neg, ← sub_eq_add_neg] at this
    have ha₁ : 0 < ‖n₁‖ := norm_pos_iff.2 h₁
    have ha₂ : 0 < ‖n₂‖ := norm_pos_iff.2 h₂
    set θ := ‖n₁‖ / (‖n₁‖ + ‖n₂‖) with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : 1 - θ = ‖n₂‖ / (‖n₁‖ + ‖n₂‖) := by rw [hθ]; field_simp; ring
    set w : E d := n₁ + θ • (n₂ - n₁) with hw
    have hw₁ : ‖w - n₁‖ < ‖n₁‖ := by
      rw [hw, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0, norm_sub_rev,
        hθ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      exact mul_lt_mul_of_pos_left hnot ha₁
    have hw₂ : ‖w - n₂‖ < ‖n₂‖ := by
      have : w - n₂ = (1 - θ) • (n₁ - n₂) := by rw [hw]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by rw [hθ1]; positivity), hθ1,
        div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      exact mul_lt_mul_of_pos_left hnot ha₂
    -- the gaps
    set g₁ := P.μ ^ 2 * (‖n₁‖ ^ 2 - ‖w - n₁‖ ^ 2) with hg₁
    set g₂ := P.μ ^ 2 * (‖n₂‖ ^ 2 - ‖w - n₂‖ ^ 2) with hg₂
    have hg₁pos : 0 < g₁ := mul_pos (by positivity)
      (sub_pos.2 (pow_lt_pow_left₀ hw₁ (norm_nonneg _) two_ne_zero))
    have hg₂pos : 0 < g₂ := mul_pos (by positivity)
      (sub_pos.2 (pow_lt_pow_left₀ hw₂ (norm_nonneg _) two_ne_zero))
    have hlim : Tendsto (fun s : ℝ ↦ s ^ 2 + 2 * s * P.μ) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun s : ℝ ↦ s ^ 2 + 2 * s * P.μ) (𝓝 0) (𝓝 (0 ^ 2 + 2 * 0 * P.μ)) :=
        (Continuous.tendsto (by fun_prop) 0)
      simpa using tendsto_nhdsWithin_of_tendsto_nhds this
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ^ 2 + 2 * s * P.μ < min g₁ g₂ ∧ s ∈ Ioo 0 P.r₀ :=
      (hlim.eventually (gt_mem_nhds (lt_min hg₁pos hg₂pos))).and
        (Ioo_mem_nhdsGT (hμ.trans C.μ_lt_r₀))
    obtain ⟨s, hs₃, hs₁, hs₂⟩ := hev.exists
    have hs₃₁ : s ^ 2 + 2 * s * P.μ < g₁ := hs₃.trans_le (min_le_left _ _)
    have hs₃₂ : s ^ 2 + 2 * s * P.μ < g₂ := hs₃.trans_le (min_le_right _ _)
    set p' : E d × ℝ := (C.xstar + P.μ • w, C.tstar - s) with hp'
    have hball : ∀ (ν : E d × ℝ) (c : E d × ℝ), c.1 = C.xstar + P.μ • ν.1 →
        c.2 = C.tstar + P.μ * ν.2 → ‖ν.1‖ ^ 2 + ν.2 ^ 2 = 1 →
        s ^ 2 + 2 * s * P.μ < P.μ ^ 2 * (‖ν.1‖ ^ 2 - ‖w - ν.1‖ ^ 2) → p' ∈ stBall c P.μ := by
      intro ν c hc1 hc2 hν hs
      rw [mem_stBall, hc1, hc2]
      have e1 : p'.1 - (C.xstar + P.μ • ν.1) = P.μ • (w - ν.1) := by
        change C.xstar + P.μ • w - (C.xstar + P.μ • ν.1) = _
        module
      have e2 : p'.2 - (C.tstar + P.μ * ν.2) = -(s + P.μ * ν.2) := by rw [hp']; ring
      rw [e1, e2, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
      have hν2 : ν.2 ≤ 1 := by nlinarith [norm_nonneg ν.1, sq_nonneg (ν.2 - 1)]
      nlinarith [sq_nonneg ν.2, mul_le_mul_of_nonneg_left hν2 (by positivity : 0 ≤ 2 * s * P.μ)]
    have hp'₁ : p' ∈ stBall C.ctr₁ P.μ :=
      hball C.ν₁ C.ctr₁ C.ctr₁_fst C.ctr₁_snd C.ν₁_unit hs₃₁
    have hp'₂ : p' ∈ stBall C.ctr₂ P.μ :=
      hball C.ν₂ C.ctr₂ C.ctr₂_fst C.ctr₂_snd C.ν₂_unit hs₃₂
    have hD : p' ∈ P.D₁ := by
      refine C.mem_D₁_of_near ?_ (by rw [hp']; dsimp only; linarith)
        (by rw [hp']; dsimp only; linarith)
      rw [hp']; dsimp only
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
      have hw' : ‖w‖ ≤ 2 := by
        have h1 : ‖w‖ ≤ ‖w - n₁‖ + ‖n₁‖ := by
          simpa using norm_add_le (w - n₁) n₁
        have := C.norm_ν₁_fst_le
        linarith
      have := C.μ_lt_r₀
      nlinarith
    have hE : p' ∈ P.E₁ := C.interior_ball p' hD hp'₁
    exact C.exterior_past p' hE hp'₂ (show C.tstar - s < C.tstar by linarith)
  have := (sameRay_iff_inv_norm_smul_eq_of_ne h₁ (neg_ne_zero.2 h₂)).1
    (sameRay_iff_norm_smul_eq.2 hray)
  rwa [norm_neg, smul_neg] at this


/-- Depth transfer. For `z ∈ B̄_μ(p̂)` with `κ(z) < r₀` and every
unit `e ∈ ℝᵈ`: `v₁(x⋆ + κ(z) e, t⋆) ≤ v₀(z)`.

Proof: `|z - (x⋆ + κ e, t̂)| ≤ μ` by the triangle inequality, i.e. `z ∈ (x⋆ + κ e, t⋆) + B`, and
`v₁ = min_{· + B} v₀` on `D₁` (`Config.v₁_eq`). -/
theorem depth_transfer {z : E d × ℝ} (hz : z ∈ stBall C.phat P.μ) {e : E d} (he : ‖e‖ = 1)
    (hκ : C.depth z < P.r₀) : P.v₁ (C.xstar + C.depth z • e, C.tstar) ≤ P.v₀ z := by
  set κ := C.depth z with hκdef
  have hκ0 : 0 ≤ κ := C.depth_nonneg hz
  set pz : E d × ℝ := (C.xstar + κ • e, C.tstar) with hpz
  have hnorm : ‖κ • e‖ = κ := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hκ0]
  have hpzD : pz ∈ P.D₁ := C.mem_D₁_of_near (by
      rw [hpz]; dsimp only; rw [add_sub_cancel_left, hnorm]; linarith [C.μ_lt_r₀, P.μ_pos])
    (by rw [hpz]; dsimp only; linarith [P.r₀_pos]) le_rfl
  have hB : z - pz ∈ P.B := by
    rw [sub_mem_B_iff, mem_stBall]
    have hz' := hz
    rw [mem_stBall, C.phat_fst] at hz'
    have ht : (z.2 - C.phat.2) ^ 2 ≤ P.μ ^ 2 := by nlinarith [norm_nonneg (z.1 - C.xstar)]
    have hsl := C.slice_sq ht
    have h1 : ‖z.1 - (C.xstar + κ • e)‖ ≤ C.slice z.2 := by
      calc ‖z.1 - (C.xstar + κ • e)‖ = ‖(z.1 - C.xstar) - κ • e‖ := by rw [sub_add_eq_sub_sub]
        _ ≤ ‖z.1 - C.xstar‖ + ‖κ • e‖ := norm_sub_le _ _
        _ = C.slice z.2 := by rw [hnorm, hκdef, ContactData.depth]; ring
    have h2 : (dualCentre P pz).2 = C.phat.2 := rfl
    simp only [dualCentre, hpz] at h2 ⊢
    rw [h2]
    have h0 : 0 ≤ ‖z.1 - (C.xstar + κ • e)‖ := norm_nonneg _
    nlinarith
  rw [P.v₁_eq hpzD]
  have := infConv_le P.isCompact_B P.continuousOn_v₀
    (fun k hk ↦ P.convStep_zero_one.closedDomain_add pz hpzD k hk) hB
  rwa [add_sub_cancel] at this


/-- The axis points `(x⋆ + k e, t⋆)`, `e = ν¹ₓ/|ν¹ₓ|`, `0 ≤ k ≤ 2μ|ν¹ₓ|`, `k ≤ 2r₀`, lie in
the interior ball `B̄_μ(p⋆ + μ ν¹)` and in `D₁`, hence in `E₁` (first step of
`NonPolar.no_nonpolar`). -/
theorem axis_mem_E₁ (h₁ : C.ν₁.1 ≠ 0) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 2 * P.μ * ‖C.ν₁.1‖)
    (hk2 : k ≤ 2 * P.r₀) :
    (C.xstar + k • (‖C.ν₁.1‖⁻¹ • C.ν₁.1), C.tstar) ∈ P.E₁ := by
  have hμ := P.μ_pos
  set a := ‖C.ν₁.1‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 h₁
  have hunit := C.ν₁_unit
  rw [← ha] at hunit
  have hnorm : ‖k • (a⁻¹ • C.ν₁.1)‖ = k := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hk0, Real.norm_of_nonneg (inv_nonneg.2 ha0.le),
      ← ha, inv_mul_cancel₀ ha0.ne', mul_one]
  refine C.interior_ball _ (C.mem_D₁_of_near ?_ ?_ le_rfl) ?_
  · change ‖C.xstar + k • (a⁻¹ • C.ν₁.1) - C.xstar‖ ≤ 2 * P.r₀
    rw [add_sub_cancel_left, hnorm]; exact hk2
  · change C.tstar - 2 * P.r₀ ≤ C.tstar; linarith [P.r₀_pos]
  · rw [← ContactData.ctr₁_eq, mem_stBall, C.ctr₁_fst, C.ctr₁_snd]
    change ‖C.xstar + k • (a⁻¹ • C.ν₁.1) - (C.xstar + P.μ • C.ν₁.1)‖ ^ 2 +
      (C.tstar - (C.tstar + P.μ * C.ν₁.2)) ^ 2 ≤ P.μ ^ 2
    have e1 : C.xstar + k • (a⁻¹ • C.ν₁.1) - (C.xstar + P.μ • C.ν₁.1) =
        (k * a⁻¹ - P.μ) • C.ν₁.1 := by module
    rw [e1, norm_smul, Real.norm_eq_abs, ← ha]
    have e2 : |k * a⁻¹ - P.μ| * a = |k - P.μ * a| := by
      rw [← abs_of_pos ha0, ← abs_mul, abs_of_pos ha0]; congr 1; field_simp
    rw [e2, sq_abs]
    nlinarith

end NonPolar

end BernoulliComparison
