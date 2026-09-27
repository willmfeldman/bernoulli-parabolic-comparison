/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.NonPolar.Collinearity
public import BernoulliComparison.Heat.Domain
public import BernoulliComparison.Barriers.Slope
public import BernoulliComparison.Touching.ClassBridge

/-!
# The sub-side axis rate

If `ν¹ₓ ≠ 0` and `e = ν¹ₓ/|ν¹ₓ|`, then `liminf_{ℓ ↓ 0} u₁(x⋆ + ℓ e, t⋆)/ℓ ≥ c₁`, stated as: for
every `ε ∈ (0, 1)`, eventually as `ℓ ↓ 0`, `(1 - ε) c₁ ℓ < u₁(x⋆ + ℓ e, t⋆)` (`NonPolar.sub_rate`).

This is the analogue of Kim (2003), Lemma 2.4 (I. C. Kim, *A free boundary problem arising in
flame propagation*, J. Differential Equations 191 (2003), 470–489). Kim bounds the rate of the
subsolution from below in every nontangential cone; here only the axis direction `e` is treated,
with an explicit barrier.

## Proof

Write `a = |ν¹ₓ|`, `b = ν¹ₜ`, `R₀ = μ a`, `t₁ = t̂ + μ b` (so `q₁ = (x⋆ + R₀ e, t₁)`), `c = c₁`.
If the claim fails, pick (after fixing all other constants) `ℓ` small with
`u₁(x⋆ + ℓ e, t⋆) ≤ m := (1 - ε) c ℓ`; then `u₀ ≤ m` on `D_ℓ = B̄_μ((x⋆ + ℓ e, t̂))`
(`u₁ = max_{· + B} u₀`). The barrier (`Barriers.subBarrier`) is
`φ(x, t) = g(|x - x⋆| - R(t)) + K |x - x_{q₁}|²`, with `g(ξ) = β' ξ - (γ/2) ξ²`,
`β' = (1 - ε/2) c`, `R(t) = R₀ - M_φ (t₁ - t)`, `M_φ = M + 2ℓ/τ`, `M = (μ + 1)/(μ a)`,
`K = m / r_L²`. On `Ω = {t₁ - τ < t < t₁} ∩ int D_ℓ ∩ {|x - x_{q₁}| < r_L} ∩ {|x - x⋆| > R(t)}`:
`(∂ₜ - Δ) φ ≥ 1` (`heat_subBarrier`), and `u₀ ≤ φ` on `∂Ω ∩ {t < t₁}` (inner sphere: `R(t)`
lies below the slice radius of the dual ball, where `u₀ = 0`; lateral side: `K r_L² = m`; outer
sphere `∂D_ℓ`: the gap is `≥ (1 - ε/16) ℓ`, `SubRateAux.outer_gap`; bottom: the gap is `≥ 2ℓ`).
`Heat.domain_comparison_sub` gives `u₀ ≤ φ` on `closure Ω`; as `E₀` misses the open dual ball, `φ`
touches `u₀` from above in `E₀` at `q₁`, where `(∂ₜ - Δ) φ ≥ 1` and `|∇φ| = β' < c`,
contradicting `TSub(O₀, E₀, u₀, c₁)`.

## Remarks on the construction

* The moving boundary is a translation, `ξ = |x - x⋆| - R(t)`, rather than a dilation of
  `|x - x⋆|`.
* The lateral cutoff is the quadratic term `K |x - x_{q₁}|²` on the spatial ball
  `|x - x_{q₁}| < r_L`, rather than an angular cutoff on a cone around `e`: the term is a
  polynomial, `Δ = 2dK`, and its gradient vanishes at `q₁`, so no smooth cutoff and no
  derivatives of the angle `(x - x⋆)·e/|x - x⋆|` are needed.
* The lower bound `R₀ - M s ≤ R_b(t₁ - s)` for `s(1 + M²) ≤ 1` is checked by squaring
  (`SubRateAux.slice_lower`), as in `AxisRate.lean`, so no concavity argument is needed.
* The window length `τ` is a fixed small constant, and `u₀` is not normalized by `c₁`.
* No transfer of the maximum is needed: at time `t₁`, `E₀` has no point with `|x - x⋆| < R₀`
  (open dual ball).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison


/-! ### The barrier and its derivatives -/

namespace Barriers

variable {d : ℕ}

/-- The barrier used for the sub-side axis rate:
`φ(x, t) = g(|x - z| - R(t)) + K |x - w|²` with `R(t) = R₀ - M (t₁ - t)` and the concave
profile `g(ξ) = β' ξ - (γ/2) ξ²`. -/
noncomputable def subBarrier (β' γ R₀ M t₁ K : ℝ) (z w : E d) (q : E d × ℝ) : ℝ :=
  radialProfile (slopeProfile β' (-(γ / 2))) (fun _ ↦ 1) (fun t ↦ M * (t₁ - t) - R₀) z q +
    (K * ‖q.1 - w‖ ^ 2 + 0)

variable {β' γ R₀ M t₁ K : ℝ} {z w : E d}

theorem subBarrier_apply (q : E d × ℝ) :
    subBarrier β' γ R₀ M t₁ K z w q =
      slopeProfile β' (-(γ / 2)) (‖q.1 - z‖ - (R₀ - M * (t₁ - q.2))) + K * ‖q.1 - w‖ ^ 2 := by
  simp only [subBarrier, radialProfile_apply]
  ring_nf

theorem contDiffOn_subBarrier :
    ContDiffOn ℝ ∞ (subBarrier β' γ R₀ M t₁ K z w) {q | q.1 ≠ z} := by
  have h1 : ContDiffOn ℝ ∞ (radialProfile (slopeProfile β' (-(γ / 2))) (fun _ ↦ 1)
      (fun t ↦ M * (t₁ - t) - R₀) z) {q | q.1 ≠ z} :=
    contDiffOn_radialProfile contDiff_slopeProfile contDiff_const
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ K * ‖q.1 - w‖ ^ 2 + 0) := by
    refine (contDiff_const.mul ?_).add contDiff_const
    exact (contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)
  exact h1.add h2.contDiffOn

theorem continuous_subBarrier_on :
    ContinuousOn (subBarrier β' γ R₀ M t₁ K z w) {q | q.1 ≠ z} :=
  contDiffOn_subBarrier.continuousOn

theorem isTestFunAt_subBarrier {p : E d × ℝ} (hp : p.1 ≠ z) :
    IsTestFunAt (subBarrier β' γ R₀ M t₁ K z w) p :=
  ⟨{q | q.1 ≠ z}, isOpen_setOf_fst_ne z, hp, contDiffOn_subBarrier⟩

/-- The heat operator of the barrier: with `ρ = |x - z| > 0` and `ξ = ρ - R(t)`,
`(∂ₜ - Δ) φ = -M g'(ξ) + γ - (d - 1) g'(ξ)/ρ - 2 d K`, `g'(ξ) = β' - γ ξ`. -/
theorem heat_subBarrier {p : E d × ℝ} (hp : p.1 ≠ z) :
    dₜ (subBarrier β' γ R₀ M t₁ K z w) p - lapₓ (subBarrier β' γ R₀ M t₁ K z w) p =
      -M * (β' - γ * (‖p.1 - z‖ - (R₀ - M * (t₁ - p.2)))) + γ -
        ((d : ℝ) - 1) * (β' - γ * (‖p.1 - z‖ - (R₀ - M * (t₁ - p.2)))) / ‖p.1 - z‖ -
          2 * d * K := by
  set ψ := radialProfile (slopeProfile β' (-(γ / 2))) (fun _ ↦ (1 : ℝ))
    (fun t ↦ M * (t₁ - t) - R₀) z with hψ
  set h : E d × ℝ → ℝ := fun q ↦ ‖q.1 - w‖ ^ 2 with hh
  have hψs : ContDiffOn ℝ ∞ ψ {q | q.1 ≠ z} :=
    contDiffOn_radialProfile contDiff_slopeProfile contDiff_const
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const)
  have hhs : ContDiff ℝ ∞ h := (contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)
  have H := dₜ_sub_lapₓ_add_mul_add_of_contDiffOn (isOpen_setOf_fst_ne z) hp hψs
    hhs.contDiffOn K 0
  have heq : (fun q ↦ ψ q + (K * h q + 0)) = subBarrier β' γ R₀ M t₁ K z w := rfl
  rw [heq] at H
  rw [H]
  have hξ : (fun _ : ℝ ↦ (1 : ℝ)) p.2 * ‖p.1 - z‖ + (M * (t₁ - p.2) - R₀) =
      ‖p.1 - z‖ - (R₀ - M * (t₁ - p.2)) := by ring
  have hdiff : DifferentiableAt ℝ (slopeProfile β' (-(γ / 2)))
      ((fun _ : ℝ ↦ (1 : ℝ)) p.2 * ‖p.1 - z‖ + (fun t ↦ M * (t₁ - t) - R₀) p.2) :=
    (hasDerivAt_slopeProfile _).differentiableAt
  have hb : HasDerivAt (fun t ↦ M * (t₁ - t) - R₀) (-M) p.2 := by
    have := (((hasDerivAt_id p.2).const_sub t₁).const_mul M).sub_const R₀
    simpa using this
  have hdt : dₜ ψ p = (β' - γ * (‖p.1 - z‖ - (R₀ - M * (t₁ - p.2)))) * (-M) := by
    rw [hψ, dₜ_radialProfile hdiff (hasDerivAt_const _ _) hb]
    simp only at hξ ⊢
    rw [hξ, deriv_slopeProfile]
    ring
  have hlap : lapₓ ψ p = -γ +
      ((d : ℝ) - 1) * (β' - γ * (‖p.1 - z‖ - (R₀ - M * (t₁ - p.2)))) / ‖p.1 - z‖ := by
    rw [hψ, lapₓ_radialProfile contDiff_slopeProfile.contDiffAt hp]
    simp only at hξ ⊢
    rw [hξ, deriv_deriv_slopeProfile, deriv_slopeProfile]
    ring
  have hdth : dₜ h p = 0 := by simp [dₜ, hh]
  have hlaph : lapₓ h p = 2 * d := by
    simp only [lapₓ, hh]
    rw [laplacian_norm_sub_sq, finrank_euclideanSpace_fin]
  rw [hdt, hlap, hdth, hlaph]
  ring

/-- The gradient of the barrier at a point with `x = w` (the quadratic term has a critical
point there): `|∇φ| = |g'(ξ)|`. -/
theorem norm_gradₓ_subBarrier {p : E d × ℝ} (hp : p.1 ≠ z) (hw : p.1 = w) :
    ‖gradₓ (subBarrier β' γ R₀ M t₁ K z w) p‖ =
      |β' - γ * (‖p.1 - z‖ - (R₀ - M * (t₁ - p.2)))| := by
  set ψ := radialProfile (slopeProfile β' (-(γ / 2))) (fun _ ↦ (1 : ℝ))
    (fun t ↦ M * (t₁ - t) - R₀) z with hψ
  set h : E d × ℝ → ℝ := fun q ↦ ‖q.1 - w‖ ^ 2 with hh
  have hψs : ContDiffOn ℝ ∞ ψ {q | q.1 ≠ z} :=
    contDiffOn_radialProfile contDiff_slopeProfile contDiff_const
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const)
  have hhs : ContDiff ℝ ∞ h := (contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)
  obtain ⟨φ, hφ, hφψ⟩ := exists_contDiff_eventuallyEq (isOpen_setOf_fst_ne z) hp hψs
  have hsum : (fun q ↦ φ q + (K * h q + 0)) =ᶠ[𝓝 p] subBarrier β' γ R₀ M t₁ K z w := by
    filter_upwards [hφψ] with q hq
    simp only [subBarrier, hq, hψ, hh]
  rw [← gradₓ_congr_of_eventuallyEq hsum,
    gradₓ_add_mul_add (hφ.differentiable (by simp)) (hhs.differentiable (by simp)),
    gradₓ_congr_of_eventuallyEq hφψ]
  have hgh : gradₓ h p = 0 := by
    simp only [gradₓ, hh]
    rw [gradient_norm_sub_sq, hw, sub_self, smul_zero]
  rw [hgh, smul_zero, add_zero]
  have hdiff : DifferentiableAt ℝ (slopeProfile β' (-(γ / 2)))
      ((fun _ : ℝ ↦ (1 : ℝ)) p.2 * ‖p.1 - z‖ + (fun t ↦ M * (t₁ - t) - R₀) p.2) :=
    (hasDerivAt_slopeProfile _).differentiableAt
  rw [hψ, norm_gradₓ_radialProfile hdiff hp, deriv_slopeProfile]
  congr 1
  ring

end Barriers


/-! ### Real-variable estimates -/

namespace NonPolar.SubRateAux

/-- Lower bound for the slice radius on a short window below `t₁`: with `R₀ = μ a`,
`a² + b² = 1`, `μ a M = μ + 1` and `s (1 + M²) ≤ 1`, `(R₀ - M s)² ≤ μ² - (μ b - s)²`. -/
theorem slice_lower {μ a b M s : ℝ} (hμ : 0 < μ) (hab : a ^ 2 + b ^ 2 = 1)
    (hM : μ * a * M = μ + 1) (hs : 0 ≤ s) (hsM : s * (1 + M ^ 2) ≤ 1) :
    (μ * a - M * s) ^ 2 ≤ μ ^ 2 - (μ * b - s) ^ 2 := by
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg (b + 1), sq_nonneg a]
  have h2 : 1 ≤ μ + 1 + μ * b := by
    have := mul_nonneg hμ.le (by linarith : (0 : ℝ) ≤ b + 1)
    linarith
  have h3 : s ^ 2 * (M ^ 2 + 1) ≤ 2 * s * (μ + 1 + μ * b) := by
    have e1 := mul_le_mul_of_nonneg_left hsM hs
    have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * s)
    have e3 : s ^ 2 * (M ^ 2 + 1) = s * (s * (1 + M ^ 2)) := by ring
    linarith
  have e4 : μ ^ 2 - (μ * b - s) ^ 2 - (μ * a - M * s) ^ 2 =
      2 * s * (μ + 1 + μ * b) - s ^ 2 * (M ^ 2 + 1) := by
    linear_combination (-μ ^ 2) * hab + 2 * s * hM
  linarith

/-- Upper bound for the slice radius: `μ² - (μ b - s)² ≤ (R₀ + (μ/R₀) s)²` for `s ≥ 0`,
`R₀ = μ a > 0`, `a² + b² = 1`. -/
theorem slice_upper {μ a b s : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hab : a ^ 2 + b ^ 2 = 1)
    (hs : 0 ≤ s) : μ ^ 2 - (μ * b - s) ^ 2 ≤ (μ * a + μ / (μ * a) * s) ^ 2 := by
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg (b - 1), sq_nonneg a]
  have hR : 0 < μ * a := mul_pos hμ ha
  have e1 : (μ * a + μ / (μ * a) * s) ^ 2 =
      (μ * a) ^ 2 + 2 * μ * s + (μ / (μ * a) * s) ^ 2 := by
    field_simp
    ring
  rw [e1]
  have e2 : μ ^ 2 - (μ * b - s) ^ 2 = (μ * a) ^ 2 + 2 * μ * b * s - s ^ 2 := by
    linear_combination (-μ ^ 2) * hab
  rw [e2]
  have := mul_le_mul_of_nonneg_left hb1 (by positivity : (0 : ℝ) ≤ 2 * μ * s)
  nlinarith [sq_nonneg (μ / (μ * a) * s), sq_nonneg s]

/-- The estimate on the outer boundary `∂D_ℓ` in the proof of `NonPolar.sub_rate`. With
`ρ = |y|`, `P = y·e`, `Y = |y - ℓ e|`, if `|y - R₀ e| ≤ r_L` (i.e. `ρ² - P² ≤ r_L²` and
`P ≥ R₀ - r_L`), `ρ ≥ 3R₀/4`, `r_L ≤ R₀ ε / 16`, `0 < ℓ < ε R₀ / 32`, then
`ρ - Y ≥ (1 - ε/16) ℓ`. -/
theorem outer_gap {ρ P Y ℓ R₀ rL ε : ℝ} (hR₀ : 0 < R₀) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hℓ : 0 < ℓ) (hℓε : ℓ < ε * R₀ / 32) (hrL0 : 0 ≤ rL) (hrL : rL ≤ R₀ * ε / 16)
    (hρ : 3 * R₀ / 4 ≤ ρ) (hY0 : 0 ≤ Y) (hY : Y ^ 2 = ρ ^ 2 - 2 * ℓ * P + ℓ ^ 2)
    (hperp : ρ ^ 2 - P ^ 2 ≤ rL ^ 2) (hP : R₀ - rL ≤ P) (hPρ : P ≤ ρ) :
    (1 - ε / 16) * ℓ ≤ ρ - Y := by
  by_contra hcon
  simp only [not_le] at hcon
  set D := ρ - Y with hD
  set Λ := (1 - ε / 16) * ℓ with hΛ
  have hDρ : D ≤ ρ := by linarith
  have hΛρ : Λ ≤ ρ := by nlinarith
  have hsum : Λ + D < 2 * ρ := by linarith
  have h2 : 2 * ρ * D - D ^ 2 = 2 * ℓ * P - ℓ ^ 2 := by
    have : Y = ρ - D := by rw [hD]; ring
    rw [this] at hY
    linarith
  have h3 : 2 * ρ * D - D ^ 2 < 2 * ρ * Λ - Λ ^ 2 := by
    have := mul_pos (sub_pos.2 hcon) (by linarith : (0 : ℝ) < 2 * ρ - Λ - D)
    nlinarith
  have h4 : 2 * ℓ * P - ℓ ^ 2 < 2 * ρ * Λ := by nlinarith [sq_nonneg Λ]
  -- `ρ - P ≤ rL² / R₀`
  have hρP0 : 0 ≤ ρ - P := by linarith
  have hsumP : R₀ ≤ ρ + P := by nlinarith
  have h5 : (ρ - P) * R₀ ≤ rL ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsumP hρP0
    nlinarith
  -- conclude
  have h6 : 2 * P - ℓ < 2 * ρ * (1 - ε / 16) := by
    have : ℓ * (2 * P - ℓ) < ℓ * (2 * ρ * (1 - ε / 16)) := by rw [hΛ] at h4; nlinarith
    exact lt_of_mul_lt_mul_left this hℓ.le
  have h7 : rL ^ 2 ≤ R₀ ^ 2 * ε / 256 := by
    have : rL ^ 2 ≤ (R₀ * ε / 16) ^ 2 := pow_le_pow_left₀ hrL0 hrL 2
    nlinarith
  have h8 : ρ * ε / 8 * R₀ < 2 * rL ^ 2 + ℓ * R₀ := by nlinarith
  nlinarith

end NonPolar.SubRateAux

namespace NonPolar

open Contact Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset}

variable (C : ContactData P)

set_option maxHeartbeats 800000 in
-- The proof is one long argument (constants, domain, comparison, touching); it exceeds the
-- default heartbeat budget.
/-- The sub-side axis rate. If `ν¹ₓ ≠ 0` and `e = ν¹ₓ/|ν¹ₓ|`, then for every
`ε ∈ (0, 1)`, eventually as `ℓ ↓ 0`: `(1 - ε) c₁ ℓ < u₁(x⋆ + ℓ e, t⋆)`.

See the module docstring for the proof and remarks on the construction of the barrier. -/
theorem sub_rate (h₁ : C.ν₁.1 ≠ 0) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ ℓ in 𝓝[>] 0,
      (1 - ε) * C.c₁ * ℓ < P.u₁ (C.xstar + ℓ • (‖C.ν₁.1‖⁻¹ • C.ν₁.1), C.tstar) := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  simp only [not_lt] at hcon
  /- ## Constants -/
  have hμ := P.μ_pos
  set c := C.c₁ with hcdef
  have hc : 0 < c := C.c₁_pos
  set a := ‖C.ν₁.1‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 h₁
  set b := C.ν₁.2 with hb
  have hab : a ^ 2 + b ^ 2 = 1 := C.ν₁_unit
  set e : E d := a⁻¹ • C.ν₁.1 with he
  have hnorm_e : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ha0.ne']
  set R₀ := P.μ * a with hR₀
  have hR₀pos : 0 < R₀ := mul_pos hμ ha0
  set t₁ := C.q₁.2 with ht₁
  have ht₁eq : t₁ = C.tstar - P.μ + P.μ * b := C.q₁_snd
  have htc : ∀ q : E d × ℝ, q.2 - (C.tstar - P.μ) = P.μ * b - (t₁ - q.2) := fun q ↦ by
    rw [ht₁eq]; ring
  set w := C.q₁.1 with hw
  have hRe : R₀ • e = P.μ • C.ν₁.1 := by
    rw [hR₀, he, smul_smul, mul_assoc, mul_inv_cancel₀ ha0.ne', mul_one]
  have hweq : w = C.xstar + R₀ • e := by rw [hRe]; exact C.q₁_fst
  have hwx : ‖w - C.xstar‖ = R₀ := by
    rw [hweq, add_sub_cancel_left, norm_smul, hnorm_e, mul_one, Real.norm_of_nonneg hR₀pos.le]
  have hwsub : ∀ x : E d, x - w = (x - C.xstar) - R₀ • e := fun x ↦ by rw [hweq]; abel
  clear hweq hRe he
  set M := (P.μ + 1) / (P.μ * a) with hM
  have hMa : P.μ * a * M = P.μ + 1 := by rw [hM]; field_simp
  have hMpos : 0 < M := by positivity
  set β' := (1 - ε / 2) * c with hβ'
  have hβ'pos : 0 < β' := mul_pos (by linarith) hc
  set γ := β' * (M + 1) + 2 * β' * |(d : ℝ) - 1| / R₀ + 2 with hγ
  have hγpos : 0 < γ := by positivity
  set L := P.μ / R₀ + M with hL
  have hLpos : 0 < L := by positivity
  set τ := min (1 / (1 + M ^ 2)) (min (R₀ / (4 * (M + 1))) (ε * c / (8 * γ * L))) with hτ
  have hτpos : 0 < τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hτ1 : τ * (1 + M ^ 2) ≤ 1 := (le_div_iff₀ (by positivity)).1 (min_le_left _ _)
  have hτ2 : (M + 1) * τ ≤ R₀ / 4 := by
    have := (le_div_iff₀ (by positivity)).1 ((min_le_right _ _).trans (min_le_left _ _) :
      τ ≤ R₀ / (4 * (M + 1)))
    linarith
  have hτ3 : γ * (L * τ) ≤ ε * c / 8 := by
    have := (le_div_iff₀ (by positivity)).1 ((min_le_right _ _).trans (min_le_right _ _) :
      τ ≤ ε * c / (8 * γ * L))
    linarith
  set rL := R₀ * ε / 16 with hrL
  have hrLpos : 0 < rL := by positivity
  set ℓ₀ := min (τ / 2) (min (ε * c / (24 * γ))
    (min (rL ^ 2 / (2 * d * c + 1)) (min (ε * R₀ / 32) P.r₀))) with hℓ₀
  have hℓ₀pos : 0 < ℓ₀ := lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) P.r₀_pos)))
  obtain ⟨ℓ, hℓu, hℓ0, hℓ1⟩ := (hcon.and_eventually (Ioo_mem_nhdsGT hℓ₀pos)).exists
  have hℓτ : ℓ ≤ τ / 2 := hℓ1.le.trans (min_le_left _ _)
  have hℓγ : ℓ ≤ ε * c / (24 * γ) := hℓ1.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hℓK : ℓ < rL ^ 2 / (2 * d * c + 1) :=
    hℓ1.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hℓR : ℓ < ε * R₀ / 32 := hℓ1.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hℓr₀ : ℓ < P.r₀ := hℓ1.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hℓγ' : 3 * γ * ℓ ≤ ε * c / 8 := by
    have := (le_div_iff₀ (by positivity)).1 hℓγ
    linarith
  have hεR : ε * R₀ / 32 < R₀ := by linarith [mul_pos (sub_pos.2 hε1) hR₀pos]
  set m := (1 - ε) * c * ℓ with hm
  have hm0 : 0 ≤ m := mul_nonneg (mul_nonneg (by linarith) hc.le) hℓ0.le
  set K := m / rL ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hKrL : K * rL ^ 2 = m := by rw [hK]; field_simp
  have h2dK : 2 * d * K ≤ 1 := by
    have h := (lt_div_iff₀ (by positivity)).1 hℓK
    have hmc : m ≤ c * ℓ := by rw [hm]; linarith [mul_pos (mul_pos hε0 hc) hℓ0]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hdm : 2 * d * m ≤ rL ^ 2 := by
      have := mul_le_mul_of_nonneg_left hmc (by positivity : (0 : ℝ) ≤ 2 * d)
      linarith
    have : 2 * d * K = 2 * d * m / rL ^ 2 := by rw [hK]; ring
    rw [this, div_le_one (by positivity)]
    exact hdm
  set Mφ := M + 2 * ℓ / τ with hMφ
  have h2ℓτ : 2 * ℓ / τ ≤ 1 := by rw [div_le_one hτpos]; linarith
  have h2ℓτ0 : 0 < 2 * ℓ / τ := by positivity
  have hMφ1 : Mφ ≤ M + 1 := by linarith
  have hMφM : M < Mφ := by linarith
  have hMφτ : Mφ * τ = M * τ + 2 * ℓ := by rw [hMφ]; field_simp
  clear_value Mφ K m ℓ₀ rL τ L γ β' M R₀ e b a c
  set φ := Barriers.subBarrier β' γ R₀ Mφ t₁ K C.xstar w with hφ
  /- ## The dual ball and the shifted ball `D_ℓ` -/
  have hdual : ∀ q : E d × ℝ,
      ‖q.1 - C.xstar‖ ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 ≤ P.μ ^ 2 → P.u₀ q = 0 :=
    fun q hq ↦ C.dual_u₀_eq_zero q hq
  have hdualopen : ∀ q : E d × ℝ,
      ‖q.1 - C.xstar‖ ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2 → q ∉ P.E₀ :=
    fun q hq ↦ C.dual_not_mem_E₀ q hq
  have hlow : ∀ s : ℝ, 0 ≤ s → s ≤ τ → (R₀ - M * s) ^ 2 ≤ P.μ ^ 2 - (P.μ * b - s) ^ 2 :=
    fun s hs0 hsτ ↦ by
      have := SubRateAux.slice_lower hμ hab hMa hs0
        ((mul_le_mul_of_nonneg_right hsτ (by positivity)).trans hτ1)
      rwa [← hR₀] at this
  have hlow0 : ∀ s : ℝ, s ≤ τ → 0 ≤ R₀ - M * s := fun s hsτ ↦ by
    have := mul_le_mul_of_nonneg_left hsτ hMpos.le
    linarith
  have hnorm_ℓe : ‖ℓ • e‖ = ℓ := by rw [norm_smul, hnorm_e, mul_one, Real.norm_of_nonneg hℓ0.le]
  set pℓ : E d × ℝ := (C.xstar + ℓ • e, C.tstar) with hpℓ
  have hpℓD : pℓ ∈ P.D₁ := C.mem_D₁_of_near
    (by rw [hpℓ]; dsimp only; rw [add_sub_cancel_left, hnorm_ℓe]; linarith [P.r₀_pos])
    (by rw [hpℓ]; dsimp only; linarith [P.r₀_pos]) le_rfl
  have hU : ∀ z : E d × ℝ,
      ‖z.1 - (C.xstar + ℓ • e)‖ ^ 2 + (z.2 - (C.tstar - P.μ)) ^ 2 ≤ P.μ ^ 2 → P.u₀ z ≤ m := by
    intro z hz
    have hB : z - pℓ ∈ P.B := by rw [sub_mem_B_iff, mem_stBall]; exact hz
    have := le_supConv P.isCompact_B P.continuousOn_u₀
      (fun k hk ↦ P.convStep_zero_one.closedDomain_add pℓ hpℓD k hk) hB
    rw [add_sub_cancel, ← P.u₁_eq hpℓD] at this
    exact this.trans hℓu
  clear hpℓ
  have hroom : ∀ z : E d × ℝ,
      ‖z.1 - (C.xstar + ℓ • e)‖ ^ 2 + (z.2 - (C.tstar - P.μ)) ^ 2 ≤ P.μ ^ 2 →
        z ∈ P.U₁ ×ˢ Ioc (2 * P.μ) T := by
    intro z hz
    have h1 : ‖z.1 - (C.xstar + ℓ • e)‖ ≤ P.μ :=
      (sq_le_sq₀ (norm_nonneg _) hμ.le).1 (by linarith [sq_nonneg (z.2 - (C.tstar - P.μ))])
    have h2 : |z.2 - (C.tstar - P.μ)| ≤ P.μ :=
      (sq_le_sq₀ (abs_nonneg _) hμ.le).1 (by
        rw [sq_abs]; linarith [sq_nonneg ‖z.1 - (C.xstar + ℓ • e)‖])
    rw [abs_le] at h2
    have hμr := C.μ_lt_r₀
    refine C.mem_room ?_ (by linarith) (by linarith)
    calc ‖z.1 - C.xstar‖ = ‖(z.1 - (C.xstar + ℓ • e)) + ℓ • e‖ := by congr 1; abel
      _ ≤ ‖z.1 - (C.xstar + ℓ • e)‖ + ‖ℓ • e‖ := norm_add_le _ _
      _ ≤ 2 * P.r₀ := by rw [hnorm_ℓe]; linarith
  have hD₀ : ∀ z : E d × ℝ,
      ‖z.1 - (C.xstar + ℓ • e)‖ ^ 2 + (z.2 - (C.tstar - P.μ)) ^ 2 ≤ P.μ ^ 2 → z ∈ P.D₀ :=
    fun z hz ↦ P.D₁_subset_D₀ (P.prod_Ioc_subset_D₁ (hroom z hz))
  /- ## The comparison domain -/
  set Ω : Set (E d × ℝ) := {q | t₁ - τ < q.2 ∧ q.2 < t₁ ∧
      ‖q.1 - (C.xstar + ℓ • e)‖ ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2 ∧
      ‖q.1 - w‖ < rL ∧ R₀ - Mφ * (t₁ - q.2) < ‖q.1 - C.xstar‖} with hΩ
  set Ωc : Set (E d × ℝ) := {q | t₁ - τ ≤ q.2 ∧ q.2 ≤ t₁ ∧
      ‖q.1 - (C.xstar + ℓ • e)‖ ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 ≤ P.μ ^ 2 ∧
      ‖q.1 - w‖ ≤ rL ∧ R₀ - Mφ * (t₁ - q.2) ≤ ‖q.1 - C.xstar‖} with hΩc
  have hΩo : IsOpen Ω := by
    rw [hΩ]
    refine IsOpen.and ?_ (IsOpen.and ?_ (IsOpen.and ?_ (IsOpen.and ?_ ?_))) <;>
      exact isOpen_lt (by fun_prop) (by fun_prop)
  have hΩcc : IsClosed Ωc := by
    rw [hΩc]
    refine IsClosed.and ?_ (IsClosed.and ?_ (IsClosed.and ?_ (IsClosed.and ?_ ?_))) <;>
      exact isClosed_le (by fun_prop) (by fun_prop)
  clear hΩ hΩc
  have hclΩ : closure Ω ⊆ Ωc := closure_minimal (fun q hq ↦
    ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.1.le, hq.2.2.2.2.le⟩) hΩcc
  /- ## Pointwise estimates on `Ωc` -/
  have hpt : ∀ q ∈ Ωc, 3 * R₀ / 4 ≤ ‖q.1 - C.xstar‖ ∧
      0 ≤ ‖q.1 - C.xstar‖ - (R₀ - Mφ * (t₁ - q.2)) ∧
      γ * (‖q.1 - C.xstar‖ - (R₀ - Mφ * (t₁ - q.2))) ≤ ε * c / 4 := by
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    set s := t₁ - q.2 with hs
    have hs0 : 0 ≤ s := by rw [hs]; linarith
    have hsτ : s ≤ τ := by rw [hs]; linarith
    have hMφs : Mφ * s ≤ (M + 1) * τ :=
      mul_le_mul hMφ1 hsτ hs0 (by linarith)
    refine ⟨by linarith, by linarith, ?_⟩
    have hup := SubRateAux.slice_upper hμ ha0 hab hs0
    rw [← hR₀] at hup
    rw [htc q] at h3
    have hY : ‖q.1 - (C.xstar + ℓ • e)‖ ≤ R₀ + P.μ / R₀ * s :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (by linarith [sq_nonneg (P.μ * b - s)])
    have hρ : ‖q.1 - C.xstar‖ ≤ ‖q.1 - (C.xstar + ℓ • e)‖ + ℓ := by
      calc ‖q.1 - C.xstar‖ = ‖(q.1 - (C.xstar + ℓ • e)) + ℓ • e‖ := by congr 1; abel
        _ ≤ ‖q.1 - (C.xstar + ℓ • e)‖ + ‖ℓ • e‖ := norm_add_le _ _
        _ = ‖q.1 - (C.xstar + ℓ • e)‖ + ℓ := by rw [hnorm_ℓe]
    have h2s : 2 * ℓ / τ * s ≤ 2 * ℓ := by
      calc 2 * ℓ / τ * s ≤ 2 * ℓ / τ * τ := mul_le_mul_of_nonneg_left hsτ h2ℓτ0.le
        _ = 2 * ℓ := by field_simp
    have hLs : P.μ / R₀ * s + M * s ≤ L * τ := by
      rw [hL, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hsτ (by positivity))
        (mul_le_mul_of_nonneg_left hsτ hMpos.le)
    have hξ : ‖q.1 - C.xstar‖ - (R₀ - Mφ * s) ≤ L * τ + 3 * ℓ := by
      have : Mφ * s = M * s + 2 * ℓ / τ * s := by linear_combination s * hMφ
      rw [this]; linarith
    calc γ * (‖q.1 - C.xstar‖ - (R₀ - Mφ * s)) ≤ γ * (L * τ + 3 * ℓ) :=
          mul_le_mul_of_nonneg_left hξ hγpos.le
      _ = γ * (L * τ) + 3 * γ * ℓ := by ring
      _ ≤ ε * c / 4 := by linarith
  have hne_of : ∀ q ∈ Ωc, q.1 ≠ C.xstar := fun q hq h ↦ by
    have := (hpt q hq).1
    rw [h, sub_self, norm_zero] at this
    linarith
  have hheat : ∀ q ∈ Ωc, 1 ≤ dₜ φ q - lapₓ φ q := by
    intro q hq
    obtain ⟨hρ, hξ0, hξ1⟩ := hpt q hq
    rw [hφ, Barriers.heat_subBarrier (hne_of q hq)]
    set ρ := ‖q.1 - C.xstar‖ with hρdef
    set ξ := ρ - (R₀ - Mφ * (t₁ - q.2)) with hξdef
    clear_value ξ ρ
    have hρpos : 0 < ρ := by linarith
    have hg0 : 0 ≤ β' - γ * ξ := by
      rw [hβ']
      linarith only [hξ1, mul_pos (show (0 : ℝ) < 1 - 3 * ε / 4 by linarith only [hε1]) hc]
    have hg1 : β' - γ * ξ ≤ β' := by linarith only [mul_nonneg hγpos.le hξ0]
    have h1 : Mφ * (β' - γ * ξ) ≤ (M + 1) * β' := mul_le_mul hMφ1 hg1 hg0 (by linarith)
    have h2 : ((d : ℝ) - 1) * (β' - γ * ξ) / ρ ≤ 2 * β' * |(d : ℝ) - 1| / R₀ := by
      have n1 : ((d : ℝ) - 1) * (β' - γ * ξ) ≤ |(d : ℝ) - 1| * β' :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) hg0).trans
          (mul_le_mul_of_nonneg_left hg1 (abs_nonneg _))
      rw [div_le_div_iff₀ hρpos hR₀pos]
      have n2 : 0 ≤ |(d : ℝ) - 1| * β' := by positivity
      have n3 := mul_le_mul_of_nonneg_right n1 hR₀pos.le
      have n4 := mul_le_mul_of_nonneg_left (by linarith only [hρ, hR₀pos] : R₀ ≤ 2 * ρ) n2
      linarith only [n3, n4]
    have h3 : γ = β' * (M + 1) + 2 * β' * |(d : ℝ) - 1| / R₀ + 2 := hγ
    linarith only [h1, h2, h3, h2dK]
  have hgprof : ∀ q ∈ Ωc, (1 - 3 * ε / 4) * c * (‖q.1 - C.xstar‖ - (R₀ - Mφ * (t₁ - q.2))) ≤
      Barriers.slopeProfile β' (-(γ / 2)) (‖q.1 - C.xstar‖ - (R₀ - Mφ * (t₁ - q.2))) := by
    intro q hq
    obtain ⟨-, hξ0, hξ1⟩ := hpt q hq
    simp only [Barriers.slopeProfile]
    have h := mul_le_mul_of_nonneg_left hξ1 hξ0
    rw [hβ']
    linarith only [h, mul_nonneg (mul_nonneg hε0.le hc.le) hξ0]
  have hglow : ∀ q ∈ Ωc,
      (1 - 3 * ε / 4) * c * (‖q.1 - C.xstar‖ - (R₀ - Mφ * (t₁ - q.2))) ≤ φ q := by
    intro q hq
    rw [hφ, Barriers.subBarrier_apply]
    have : 0 ≤ K * ‖q.1 - w‖ ^ 2 := mul_nonneg hK0 (sq_nonneg _)
    linarith only [hgprof q hq, this]
  have hφ0 : ∀ q ∈ Ωc, 0 ≤ φ q := fun q hq ↦
    le_trans (mul_nonneg (mul_nonneg (by linarith) hc.le) (hpt q hq).2.1) (hglow q hq)
  /- ## Boundary ordering -/
  have hbdry : ∀ p ∈ frontier Ω, p.2 < t₁ → P.u₀ p ≤ φ p := by
    intro p hp hpt₁
    rw [hΩo.frontier_eq] at hp
    obtain ⟨hpcl, hpnot⟩ := hp
    have hpc := hclΩ hpcl
    obtain ⟨h1, h2, h3, h4, h5⟩ := id hpc
    have hum := hU p h3
    have hgl := hglow p hpc
    obtain ⟨hρ, hξ0, -⟩ := hpt p hpc
    set s := t₁ - p.2 with hs
    have hs0 : 0 ≤ s := by rw [hs]; linarith
    have hsτ : s ≤ τ := by rw [hs]; linarith
    have hts := htc p
    by_cases hb1 : t₁ - τ < p.2
    · by_cases hb3 : ‖p.1 - (C.xstar + ℓ • e)‖ ^ 2 + (p.2 - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2
      · by_cases hb4 : ‖p.1 - w‖ < rL
        · -- the inner sphere is active: `p` lies in the closed dual ball
          have hb5 : ‖p.1 - C.xstar‖ ≤ R₀ - Mφ * s :=
            not_lt.1 fun h ↦ hpnot ⟨hb1, hpt₁, hb3, hb4, h⟩
          have hMs : R₀ - Mφ * s ≤ R₀ - M * s := by
            linarith [mul_le_mul_of_nonneg_right hMφM.le hs0]
          have hsq : ‖p.1 - C.xstar‖ ^ 2 ≤ (R₀ - M * s) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hb5.trans hMs) 2
          rw [hdual p (by rw [hts]; linarith [hlow s hs0 hsτ])]
          exact hφ0 p hpc
        · -- the lateral boundary is active
          have hlat : ‖p.1 - w‖ = rL := le_antisymm h4 (not_lt.1 hb4)
          rw [hφ, Barriers.subBarrier_apply, hlat, hKrL]
          have : 0 ≤ (1 - 3 * ε / 4) * c * (‖p.1 - C.xstar‖ - (R₀ - Mφ * (t₁ - p.2))) :=
            mul_nonneg (mul_nonneg (by linarith) hc.le) hξ0
          linarith only [hgprof p hpc, this, hum]
      · -- the outer sphere `∂D_ℓ` is active
        have hout : ‖p.1 - (C.xstar + ℓ • e)‖ ^ 2 + (p.2 - (C.tstar - P.μ)) ^ 2 = P.μ ^ 2 :=
          le_antisymm h3 (not_lt.1 hb3)
        set y := p.1 - C.xstar with hy
        set Y := ‖p.1 - (C.xstar + ℓ • e)‖ with hYdef
        have hyY : p.1 - (C.xstar + ℓ • e) = y - ℓ • e := by rw [hy]; abel
        have hyw : p.1 - w = y - R₀ • e := by rw [hy, hwsub]
        have hY2 : Y ^ 2 = ‖y‖ ^ 2 - 2 * ℓ * inner ℝ y e + ℓ ^ 2 := by
          rw [hYdef, hyY, norm_sub_sq_real, inner_smul_right, hnorm_ℓe]; ring
        have hW2 : ‖p.1 - w‖ ^ 2 = ‖y‖ ^ 2 - 2 * R₀ * inner ℝ y e + R₀ ^ 2 := by
          rw [hyw, norm_sub_sq_real, inner_smul_right, norm_smul, hnorm_e,
            Real.norm_of_nonneg hR₀pos.le]; ring
        have hPρ : inner ℝ y e ≤ ‖y‖ := by
          have := real_inner_le_norm y e
          rwa [hnorm_e, mul_one] at this
        have hPρ2 : inner ℝ y e ^ 2 ≤ ‖y‖ ^ 2 := by
          have := abs_real_inner_le_norm y e
          rw [hnorm_e, mul_one] at this
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        have hw2 : ‖p.1 - w‖ ^ 2 ≤ rL ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
        have hperp : ‖y‖ ^ 2 - inner ℝ y e ^ 2 ≤ rL ^ 2 := by
          linarith [sq_nonneg (inner ℝ y e - R₀)]
        have hP : R₀ - rL ≤ inner ℝ y e := by
          have : (inner ℝ y e - R₀) ^ 2 ≤ rL ^ 2 := by linarith
          have := abs_le_of_sq_le_sq' this hrLpos.le
          linarith [this.1]
        have hgap := SubRateAux.outer_gap hR₀pos hε0 hε1 hℓ0 hℓR hrLpos.le hrL.le hρ
          (norm_nonneg _) hY2 hperp hP hPρ
        -- `R(t) ≤ Y`
        have hYR : R₀ - M * s ≤ Y := by
          have hsq : (R₀ - M * s) ^ 2 ≤ Y ^ 2 := by
            have := hlow s hs0 hsτ
            rw [hts] at hout
            linarith
          exact (sq_le_sq₀ (hlow0 s hsτ) (norm_nonneg _)).1 hsq
        have hMs : R₀ - Mφ * s ≤ R₀ - M * s := by
          linarith [mul_le_mul_of_nonneg_right hMφM.le hs0]
        have hξ : (1 - ε / 16) * ℓ ≤ ‖y‖ - (R₀ - Mφ * s) := by linarith
        have hfin : m ≤ (1 - 3 * ε / 4) * c * (‖y‖ - (R₀ - Mφ * s)) := by
          have hcoef : 0 ≤ (1 - 3 * ε / 4) * c := mul_nonneg (by linarith) hc.le
          calc m = (1 - ε) * c * ℓ := hm
            _ ≤ (1 - 3 * ε / 4) * c * ((1 - ε / 16) * ℓ) := by
              linarith [mul_nonneg (mul_nonneg hc.le hℓ0.le) hε0.le,
                mul_nonneg (mul_nonneg hc.le hℓ0.le) (sq_nonneg ε)]
            _ ≤ _ := mul_le_mul_of_nonneg_left hξ hcoef
        linarith
    · -- the bottom is active: `s = τ`
      have hsτ' : s = τ := by rw [hs]; linarith
      by_cases hin : ‖p.1 - C.xstar‖ ^ 2 + (p.2 - (C.tstar - P.μ)) ^ 2 ≤ P.μ ^ 2
      · rw [hdual p hin]; exact hφ0 p hpc
      · have hbig : (R₀ - M * τ) ^ 2 < ‖p.1 - C.xstar‖ ^ 2 := by
          have := hlow τ hτpos.le le_rfl
          rw [hts, ← hs, hsτ'] at hin
          linarith
        have hρ' : R₀ - M * τ < ‖p.1 - C.xstar‖ :=
          (sq_lt_sq₀ (hlow0 τ le_rfl) (norm_nonneg _)).1 hbig
        have hξ : 2 * ℓ < ‖p.1 - C.xstar‖ - (R₀ - Mφ * s) := by rw [hsτ', hMφτ]; linarith
        have hfin : m ≤ (1 - 3 * ε / 4) * c * (‖p.1 - C.xstar‖ - (R₀ - Mφ * s)) := by
          have hcoef : 0 ≤ (1 - 3 * ε / 4) * c := mul_nonneg (by linarith) hc.le
          calc m = (1 - ε) * c * ℓ := hm
            _ ≤ (1 - 3 * ε / 4) * c * (2 * ℓ) := by
              linarith [mul_nonneg (mul_nonneg hc.le hℓ0.le) hε0.le, mul_nonneg hc.le hℓ0.le]
            _ ≤ _ := mul_le_mul_of_nonneg_left hξ.le hcoef
        linarith
  /- ## Comparison in `Ω` -/
  have hΩsub : Ω ⊆ P.U₀ ×ˢ Ioc 0 T := fun q hq ↦ by
    have h := hroom q hq.2.2.1.le
    exact ⟨P.U₁_subset_U₀ h.1, by linarith [h.2.1], h.2.2⟩
  have hΩb : Bornology.IsBounded Ω := by
    refine (Metric.isBounded_closedBall (x := ((C.xstar + ℓ • e, C.tstar - P.μ) : E d × ℝ))
      (r := |P.μ|)).subset fun q hq ↦ stBall_subset_closedBall _ _ ?_
    exact hq.2.2.1.le
  have hclD₀ : closure Ω ⊆ P.D₀ := fun q hq ↦ hD₀ q (hclΩ hq).2.2.1
  have hclne : closure Ω ⊆ {q | q.1 ≠ C.xstar} := fun q hq ↦ hne_of q (hclΩ hq)
  have hcomp := Heat.domain_comparison_sub (T₁ := t₁) (b := φ) hΩo hΩb (fun q hq ↦ hq.2.1)
    ((P.isSubcal_zero.restrict hΩsub hΩo.isParOpen).isCaloricSub)
    (P.continuousOn_u₀.mono hclD₀) (Barriers.continuous_subBarrier_on.mono hclne)
    (Barriers.contDiffOn_subBarrier.mono (subset_closure.trans hclne))
    (fun q hq ↦ by linarith [hheat q (hclΩ (subset_closure hq))]) hbdry
  /- ## Touching at `q₁` -/
  set S : Set (E d × ℝ) := {q | ‖q.1 - (C.xstar + ℓ • e)‖ ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 <
      P.μ ^ 2 ∧ ‖q.1 - w‖ < rL ∧ t₁ - τ < q.2} with hS
  have hSo : IsOpen S := by
    rw [hS]
    refine IsOpen.and ?_ (IsOpen.and ?_ ?_) <;> exact isOpen_lt (by fun_prop) (by fun_prop)
  clear hS
  have hq₁out : ‖C.q₁.1 - (C.xstar + ℓ • e)‖ ^ 2 + (C.q₁.2 - (C.tstar - P.μ)) ^ 2 <
      P.μ ^ 2 := by
    have e1 : C.q₁.1 - (C.xstar + ℓ • e) = (R₀ - ℓ) • e := by
      rw [← hw, ← neg_sub, hwsub]; module
    have e2 : C.q₁.2 - (C.tstar - P.μ) = P.μ * b := by rw [← ht₁, ht₁eq]; ring
    rw [e1, e2, norm_smul, hnorm_e, mul_one, Real.norm_eq_abs, sq_abs]
    have : R₀ ^ 2 + (P.μ * b) ^ 2 = P.μ ^ 2 := by rw [hR₀]; linear_combination P.μ ^ 2 * hab
    linarith [mul_pos hℓ0 (by linarith : (0 : ℝ) < 2 * R₀ - ℓ)]
  have hq₁S : C.q₁ ∈ S := ⟨hq₁out, by rw [← hw, sub_self, norm_zero]; exact hrLpos,
    by rw [← ht₁]; linarith⟩
  obtain ⟨r, hr, hrS⟩ := exists_parCyl_of_eventually (hSo.mem_nhds hq₁S)
  have hq₁ne : C.q₁.1 ≠ C.xstar := fun h ↦ by
    rw [← hw] at h; rw [h, sub_self, norm_zero] at hwx; linarith
  have hφq₁ : φ C.q₁ = 0 := by
    rw [hφ, Barriers.subBarrier_apply, ← hw, ← ht₁, hwx]
    simp [Barriers.slopeProfile]
  have hq₁Ωc : C.q₁ ∈ Ωc := ⟨by rw [← ht₁]; linarith, by rw [← ht₁], hq₁out.le,
    by rw [← hw, sub_self, norm_zero]; exact hrLpos.le, by rw [← hw, ← ht₁, hwx]; simp⟩
  have hcross : CrossesFromAbove P.E₀ P.u₀ φ C.q₁ := by
    refine ⟨C.q₁_mem_E₀, by rw [C.u₀_q₁, hφq₁], r, hr, fun z hz ↦ ?_⟩
    obtain ⟨hzE, hzc⟩ := hz
    obtain ⟨hS1, hS2, hS3⟩ := hrS z hzc
    have hzt : z.2 ≤ t₁ := (mem_parCyl.1 hzc).2.2
    have hts := htc z
    rcases lt_or_eq_of_le hzt with hlt | heq
    · by_cases hR : R₀ - Mφ * (t₁ - z.2) < ‖z.1 - C.xstar‖
      · exact hcomp z (subset_closure ⟨hS3, hlt, hS1, hS2, hR⟩)
      · exfalso
        set s := t₁ - z.2 with hs
        have hs0 : 0 < s := by rw [hs]; linarith
        have hsτ : s ≤ τ := by rw [hs]; linarith
        have hMs : R₀ - Mφ * s < R₀ - M * s := by
          linarith [mul_lt_mul_of_pos_right hMφM hs0]
        have hρ : ‖z.1 - C.xstar‖ < R₀ - M * s := (not_lt.1 hR).trans_lt hMs
        have hsq : ‖z.1 - C.xstar‖ ^ 2 < (R₀ - M * s) ^ 2 :=
          pow_lt_pow_left₀ hρ (norm_nonneg _) two_ne_zero
        exact hdualopen z (by rw [hts]; linarith [hlow s hs0.le hsτ]) hzE
    · have hz2 : z.2 - (C.tstar - P.μ) = P.μ * b := by rw [hts, heq, sub_self, sub_zero]
      have hμb : R₀ ^ 2 + (P.μ * b) ^ 2 = P.μ ^ 2 := by
        rw [hR₀]; linear_combination P.μ ^ 2 * hab
      rcases lt_trichotomy ‖z.1 - C.xstar‖ R₀ with h | h | h
      · exfalso
        have hsq : ‖z.1 - C.xstar‖ ^ 2 < R₀ ^ 2 := pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
        exact hdualopen z (by rw [hz2]; linarith) hzE
      · have hφz : φ z = K * ‖z.1 - w‖ ^ 2 := by
          rw [hφ, Barriers.subBarrier_apply, h, heq]
          simp [Barriers.slopeProfile]
        rw [hdual z (by rw [hz2, h]; linarith), hφz]
        exact mul_nonneg hK0 (sq_nonneg _)
      · have hmem : z ∈ closure Ω := by
          have htend : Tendsto (fun σ : ℝ ↦ ((z.1, t₁ - σ) : E d × ℝ)) (𝓝[>] 0) (𝓝 z) := by
            have : Tendsto (fun σ : ℝ ↦ ((z.1, t₁ - σ) : E d × ℝ)) (𝓝 0) (𝓝 (z.1, t₁ - 0)) :=
              Continuous.tendsto (by fun_prop) 0
            have hz' : ((z.1, t₁ - 0) : E d × ℝ) = z := by rw [sub_zero, ← heq]
            rw [hz'] at this
            exact tendsto_nhdsWithin_of_tendsto_nhds this
          have hev1 : ∀ᶠ σ in 𝓝[>] (0 : ℝ),
              ‖z.1 - (C.xstar + ℓ • e)‖ ^ 2 + (t₁ - σ - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2 := by
            have hc' : Tendsto (fun σ : ℝ ↦
                ‖z.1 - (C.xstar + ℓ • e)‖ ^ 2 + (t₁ - σ - (C.tstar - P.μ)) ^ 2) (𝓝[>] 0)
                (𝓝 (‖z.1 - (C.xstar + ℓ • e)‖ ^ 2 + (t₁ - 0 - (C.tstar - P.μ)) ^ 2)) :=
              tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto (by fun_prop) 0)
            refine hc'.eventually (gt_mem_nhds ?_)
            rw [sub_zero, ← heq]
            exact hS1
          refine mem_closure_of_tendsto htend ((hev1.and (Ioo_mem_nhdsGT hτpos)).mono
            fun σ hσ ↦ ?_)
          obtain ⟨hσ1, hσ2, hσ3⟩ := hσ
          refine ⟨?_, ?_, hσ1, hS2, ?_⟩
          · change t₁ - τ < t₁ - σ
            linarith
          · change t₁ - σ < t₁
            linarith
          · change R₀ - Mφ * (t₁ - (t₁ - σ)) < ‖z.1 - C.xstar‖
            have : 0 ≤ Mφ * σ := mul_nonneg (by linarith) hσ2.le
            rw [sub_sub_cancel]
            linarith
        exact hcomp z hmem
  /- ## Contradiction with `TSub(O₀, E₀, u₀, c₁)` -/
  rcases C.touchSub_zero C.q₁ ⟨C.q₁_mem_E₀, C.q₁_mem_O₀⟩ φ
      (Barriers.isTestFunAt_subBarrier hq₁ne) hcross with hH | ⟨-, hgrad⟩
  · linarith [hheat _ hq₁Ωc]
  · rw [hφ, Barriers.norm_gradₓ_subBarrier hq₁ne rfl, ← hw, ← ht₁, hwx] at hgrad
    simp only [sub_self, mul_zero, sub_zero] at hgrad
    rw [abs_of_pos hβ'pos, ← hcdef, hβ'] at hgrad
    linarith [mul_pos hε0 hc]

end NonPolar

end BernoulliComparison
