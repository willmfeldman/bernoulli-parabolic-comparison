/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.Crossing
public import BernoulliComparison.Touching.Calculus
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The touching bridge: barrier solutions satisfy the touching alternatives

The solution classes of this project are the barrier ones (`IsParaRelaxedSub`, `IsParaSuper`).
Here we prove that they satisfy the pointwise touching alternatives of the classical
test-function definitions of viscosity (relaxed) subsolutions and supersolutions:

* `IsParaRelaxedSub.touching_alt`: if a `C^∞` function `φ` crosses `u` from above in `E` at
  `p ∈ U × I`, then `(∂ₜφ - Δφ)(p) ≤ 0`, or `φ(p) = 0` and `Q(x₀) ≤ |∇φ(p)|`;
* `IsParaSuper.touching_alt`: if `φ` crosses `v` from below in `U × I` at `p`, then
  `(∂ₜφ - Δφ)(p) ≥ 0`, or `φ(p) = 0` and `|∇φ(p)| ≤ Q(x₀)`.

## Proof (sub case; the super case is dual)

Suppose both alternatives fail at `p = (x₀, t₀)`. Put
`h₁(x, t) = |x - x₀|² + (t₀ - t)` and `ψ = φ + η h₁ - c` with `0 < c < η r²`. Then `ψ(p) < φ(p)`,
while `ψ ≥ φ + η r² - c > φ` on the parabolic boundary of `B_r(x₀) × (t₀ - r², t₀]`, where
`h₁ ≥ r²`. For `η` and then `r` small, `ψ` is a classical strict supersolution on the closed
cylinder: `∂ₜψ - Δψ = (∂ₜφ - Δφ) + η (∂ₜh₁ - Δh₁) > 0` by continuity, and either `ψ > 0` on the
closed cylinder (if `φ(p) > 0`), so that `∂{ψ > 0}` misses it, or `|∇ψ| < Q` there (if
`|∇φ(p)| < Q(x₀)`, using continuity of `Q` at `x₀`). The barrier clause then gives
`u(p) < ψ(p) = u(p) - c`, a contradiction.

Only the continuity of `Q` at `x₀` is used, and only in the gradient alternative.

The domain hypotheses at `p` are `p.1 ∈ U`, `U` open, and `I ∈ 𝓝[≤] p.2` (the backward time
interval near `p.2` is in `I`; e.g. `p.2 ∈ Ioc 0 T`, `I = Ioc 0 T`).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Closed backward cylinders -/

/-- The closed backward cylinder `B̄_r(x) × [t - r², t]`. -/
def closedParCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := closedBall x r ×ˢ Icc (t - r ^ 2) t

theorem mem_closedParCyl {x : E d} {t r : ℝ} {q : E d × ℝ} :
    q ∈ closedParCyl x t r ↔ dist q.1 x ≤ r ∧ t - r ^ 2 ≤ q.2 ∧ q.2 ≤ t := by
  simp [closedParCyl, mem_prod, mem_closedBall]

/-- A property holding near `p` holds on all small closed backward cylinders at `p`. -/
theorem eventually_forall_closedParCyl {p : E d × ℝ} {P : E d × ℝ → Prop}
    (h : ∀ᶠ q in 𝓝 p, P q) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ q ∈ closedParCyl p.1 p.2 r, P q := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
  filter_upwards [Ioo_mem_nhdsGT (lt_min hε one_pos)] with r ⟨hr0, hr⟩ q hq
  obtain ⟨hq1, hq2, hq3⟩ := mem_closedParCyl.1 hq
  have h1 := min_le_left ε 1
  have h2 := min_le_right ε 1
  apply hball
  rw [Prod.dist_eq]
  refine max_lt (hq1.trans_lt (hr.trans_le h1)) ?_
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

/-- Small closed backward cylinders at `p` lie in `U × I`. -/
theorem eventually_closedParCyl_subset_prod {U : Set (E d)} {I : Set ℝ} {p : E d × ℝ}
    (hU : IsOpen U) (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), closedParCyl p.1 p.2 r ⊆ U ×ˢ I := by
  obtain ⟨ε, hε, hballU⟩ := Metric.isOpen_iff.1 hU _ hpU
  obtain ⟨l, hl, hIcc⟩ := mem_nhdsLE_iff_exists_Icc_subset.1 hpI
  have hδ : 0 < min ε (min 1 (p.2 - l)) := lt_min hε (lt_min one_pos (by linarith))
  filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨hr0, hr⟩ q hq
  obtain ⟨hq1, hq2, hq3⟩ := mem_closedParCyl.1 hq
  have h1 := min_le_left ε (min 1 (p.2 - l))
  have h2 := min_le_right ε (min 1 (p.2 - l))
  have h3 := min_le_left 1 (p.2 - l)
  have h4 := min_le_right 1 (p.2 - l)
  refine ⟨hballU (mem_ball.2 (hq1.trans_lt (by linarith))), hIcc ⟨?_, hq3⟩⟩
  nlinarith

/-- Small closed backward cylinders at `(x, t)` lie in the open backward cylinder of radius
`r₀`. -/
theorem eventually_closedParCyl_subset_parCyl {x : E d} {t r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), closedParCyl x t r ⊆ parCyl x t r₀ := by
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r ⟨hr0, hr⟩ q hq
  obtain ⟨hq1, hq2, hq3⟩ := mem_closedParCyl.1 hq
  exact mem_parCyl.2 ⟨hq1.trans_lt hr, by nlinarith, hq3⟩

theorem eventually_mul_sq_lt (η : ℝ) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), η * r ^ 2 < g := by
  have hc : Continuous fun r : ℝ ↦ η * r ^ 2 := continuous_const.mul (continuous_pow 2)
  have : Tendsto (fun r : ℝ ↦ η * r ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto 0
  exact (this.eventually (gt_mem_nhds hg)).filter_mono nhdsWithin_le_nhds

/-- The parabolic boundary of `B_r(x) × (t - r², t]` lies in the closed cylinder. -/
theorem parBdry_ball_subset_closedParCyl {x : E d} {t r : ℝ} (hr : 0 < r) :
    parBdry (ball x r) (t - r ^ 2) t ⊆ closedParCyl x t r := by
  rw [parBdry, closure_ball x hr.ne', frontier_ball x hr.ne']
  rintro q (⟨hq1, hq2⟩ | ⟨hq1, hq2⟩)
  · rw [mem_singleton_iff] at hq2
    exact ⟨hq1, by rw [hq2]; exact ⟨le_rfl, by nlinarith⟩⟩
  · exact ⟨sphere_subset_closedBall hq1, hq2⟩

theorem admissibleCyl_ball {U : Set (E d)} {I : Set ℝ} {x : E d} {t r : ℝ} (hr : 0 < r)
    (hsub : closedParCyl x t r ⊆ U ×ˢ I) : AdmissibleCyl U I (ball x r) (t - r ^ 2) t :=
  ⟨isOpen_ball, isBounded_ball, by nlinarith, by rw [closure_ball x hr.ne']; exact hsub⟩

theorem mem_cyl_ball {p : E d × ℝ} {r : ℝ} (hr : 0 < r) :
    p ∈ cyl (ball p.1 r) (p.2 - r ^ 2) p.2 :=
  ⟨mem_ball_self hr, by nlinarith, le_rfl⟩

/-! ### The auxiliary function `h₁(x, t) = |x - x₀|² + (t₀ - t)` -/

/-- `bumpP p q = |q.1 - p.1|² + (p.2 - q.2)`: vanishes at `p`, is `≥ r²` on the parabolic
boundary of the backward cylinder of radius `r` at `p`. -/
noncomputable def bumpP (p : E d × ℝ) (q : E d × ℝ) : ℝ := ‖q.1 - p.1‖ ^ 2 + (p.2 - q.2)

theorem contDiff_bumpP (p : E d × ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (bumpP p) :=
  ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)).add
    (contDiff_const.sub contDiff_snd)

@[simp] theorem bumpP_self (p : E d × ℝ) : bumpP p p = 0 := by simp [bumpP]

theorem bumpP_nonneg {p q : E d × ℝ} (hq : q.2 ≤ p.2) : 0 ≤ bumpP p q := by
  unfold bumpP; nlinarith [sq_nonneg ‖q.1 - p.1‖]

theorem bumpP_le {p q : E d × ℝ} {r : ℝ} (hq : q ∈ closedParCyl p.1 p.2 r) :
    bumpP p q ≤ 2 * r ^ 2 := by
  obtain ⟨hq1, hq2, hq3⟩ := mem_closedParCyl.1 hq
  rw [dist_eq_norm] at hq1
  unfold bumpP
  nlinarith [norm_nonneg (q.1 - p.1)]

theorem sq_le_bumpP {p q : E d × ℝ} {r : ℝ} (hr : 0 < r)
    (hq : q ∈ parBdry (ball p.1 r) (p.2 - r ^ 2) p.2) : r ^ 2 ≤ bumpP p q := by
  rw [parBdry, closure_ball _ hr.ne', frontier_ball _ hr.ne'] at hq
  unfold bumpP
  rcases hq with ⟨-, hq2⟩ | ⟨hq1, -, hq3⟩
  · rw [mem_singleton_iff] at hq2
    rw [hq2]; nlinarith [sq_nonneg ‖q.1 - p.1‖]
  · rw [mem_sphere, dist_eq_norm] at hq1
    rw [hq1]; linarith

/-! ### Uniform bounds for the operators of `h₁` near `p` -/

theorem exists_bound_bumpP (p : E d × ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ᶠ q in 𝓝 p,
      |dₜ (bumpP p) q - lapₓ (bumpP p) q| ≤ M ∧ ‖gradₓ (bumpP p) q‖ ≤ M := by
  have h2 : ContDiff ℝ 2 (bumpP p) := contDiff_bumpP p
  have h1 : ContDiff ℝ 1 (bumpP p) := contDiff_bumpP p
  have hF : Continuous fun q ↦ |dₜ (bumpP p) q - lapₓ (bumpP p) q| :=
    ((continuous_dₜ h1).sub (continuous_lapₓ h2)).abs
  have hG : Continuous fun q ↦ ‖gradₓ (bumpP p) q‖ := (continuous_gradₓ h1).norm
  set M := |dₜ (bumpP p) p - lapₓ (bumpP p) p| + ‖gradₓ (bumpP p) p‖ + 1
  refine ⟨M, by positivity, ?_⟩
  have e1 := hF.continuousAt.eventually_lt (continuous_const (y := M)).continuousAt
    (by simp only [M]; linarith [norm_nonneg (gradₓ (bumpP p) p)])
  have e2 := hG.continuousAt.eventually_lt (continuous_const (y := M)).continuousAt
    (by simp only [M]; linarith [abs_nonneg (dₜ (bumpP p) p - lapₓ (bumpP p) p)])
  filter_upwards [e1, e2] with q hq1 hq2 using ⟨hq1.le, hq2.le⟩

/-- Choice of the perturbation size `η`. -/
theorem exists_eta {M κ : ℝ} (hM : 0 ≤ M) (hκ : 0 < κ) : ∃ η > 0, η * M < κ := by
  refine ⟨κ / (M + 1), by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

/-! ### Relaxed subsolutions -/

section Sub

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ} {S : Set (E d × ℝ)}
  {φ : E d × ℝ → ℝ} {p : E d × ℝ}

/-- Core of the relaxed-subsolution bridge: if `φ` crosses `u` from above in `S` at `p`, the heat
operator of `φ` at `p` cannot be positive while `φ(p) > 0` or `|∇φ(p)| < Q(x₀)` (the latter
with `Q` continuous at `x₀`). -/
theorem IsParaRelaxedSub.false_of_crossesFromAbove (hsub : IsParaRelaxedSub U Q I u S)
    (hU : IsOpen U) (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) (hφ : ContDiff ℝ ∞ φ)
    (hcross : CrossesFromAbove S u φ p) (hH : 0 < dₜ φ p - lapₓ φ p)
    (hfront : 0 < φ p ∨ (ContinuousAt Q p.1 ∧ ‖gradₓ φ p‖ < Q p.1)) : False := by
  set H := dₜ φ p - lapₓ φ p with hHdef
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  set h₁ := bumpP p with hh₁def
  have hh₁ : ContDiff ℝ ∞ h₁ := contDiff_bumpP p
  have hh₁2 : ContDiff ℝ 2 h₁ := contDiff_bumpP p
  have hh₁d : Differentiable ℝ h₁ := (contDiff_bumpP p (n := 1)).differentiable one_ne_zero
  obtain ⟨M, hM0, hMev⟩ := exists_bound_bumpP p
  -- heat operator of `φ` stays above `H / 2` near `p`
  have hHev : ∀ᶠ q in 𝓝 p, H / 2 < dₜ φ q - lapₓ φ q :=
    continuousAt_const.eventually_lt ((continuous_dₜ hφ1).sub (continuous_lapₓ hφ2)).continuousAt
      (by linarith)
  -- margin `g` for the free-boundary condition
  obtain ⟨g, hg, hgev⟩ : ∃ g > 0, (∀ᶠ q in 𝓝 p, 2 * g < φ q) ∨
      (∀ᶠ q in 𝓝 p, ‖gradₓ φ q‖ + 2 * g < Q q.1) := by
    rcases hfront with hpos | ⟨hQ, hgrad⟩
    · refine ⟨φ p / 4, by positivity, Or.inl ?_⟩
      exact continuousAt_const.eventually_lt hφ.continuous.continuousAt (by linarith)
    · refine ⟨(Q p.1 - ‖gradₓ φ p‖) / 4, by linarith, Or.inr ?_⟩
      exact (((continuous_gradₓ hφ1).norm.add continuous_const).continuousAt).eventually_lt
        (hQ.comp continuousAt_fst) (by simp only [Pi.add_apply]; linarith)
  obtain ⟨η, hη, hηM⟩ := exists_eta hM0 (lt_min (half_pos hH) hg)
  have hηH : η * M < H / 2 := hηM.trans_le (min_le_left _ _)
  have hηg : η * M < g := hηM.trans_le (min_le_right _ _)
  have hpS : p ∈ S := hcross.1
  obtain ⟨r₀, hr₀pos, hle⟩ := hcross.2.2
  -- choice of the radius `r`
  have hrev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ closedParCyl p.1 p.2 r ⊆ U ×ˢ I ∧
      closedParCyl p.1 p.2 r ⊆ parCyl p.1 p.2 r₀ ∧ η * r ^ 2 < g ∧
      (∀ q ∈ closedParCyl p.1 p.2 r, (|dₜ h₁ q - lapₓ h₁ q| ≤ M ∧ ‖gradₓ h₁ q‖ ≤ M) ∧
        H / 2 < dₜ φ q - lapₓ φ q) ∧
      ((∀ q ∈ closedParCyl p.1 p.2 r, 2 * g < φ q) ∨
        (∀ q ∈ closedParCyl p.1 p.2 r, ‖gradₓ φ q‖ + 2 * g < Q q.1)) := by
    have hfr : ∀ᶠ r in 𝓝[>] (0 : ℝ), ((∀ q ∈ closedParCyl p.1 p.2 r, 2 * g < φ q) ∨
        (∀ q ∈ closedParCyl p.1 p.2 r, ‖gradₓ φ q‖ + 2 * g < Q q.1)) := by
      rcases hgev with h | h
      · exact (eventually_forall_closedParCyl h).mono fun r hr ↦ Or.inl hr
      · exact (eventually_forall_closedParCyl h).mono fun r hr ↦ Or.inr hr
    filter_upwards [self_mem_nhdsWithin, eventually_closedParCyl_subset_prod hU hpU hpI,
      eventually_closedParCyl_subset_parCyl hr₀pos, eventually_mul_sq_lt η hg,
      eventually_forall_closedParCyl (hMev.and hHev), hfr] with r h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨r, hr, hsubUI, hsubCyl, hηr, hbounds, hfr⟩ := hrev.exists
  -- the perturbed test function
  set c := η * r ^ 2 / 2 with hcdef
  have hc : 0 < c := by positivity
  set ψ : E d × ℝ → ℝ := fun q ↦ φ q + (η * h₁ q + -c) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := hφ.add ((contDiff_const.mul hh₁).add contDiff_const)
  have hψheat : ∀ q, dₜ ψ q - lapₓ ψ q = (dₜ φ q - lapₓ φ q) + η * (dₜ h₁ q - lapₓ h₁ q) :=
    dₜ_sub_lapₓ_add_mul_add hφ2 hh₁2 η (-c)
  have hψgrad : ∀ q, gradₓ ψ q = gradₓ φ q + η • gradₓ h₁ q :=
    gradₓ_add_mul_add hφd hh₁d η (-c)
  have hclosure : closure (ball p.1 r) ×ˢ Icc (p.2 - r ^ 2) p.2 = closedParCyl p.1 p.2 r := by
    rw [closure_ball _ hr.ne']; rfl
  -- `ψ` is a classical strict supersolution on the closed cylinder
  have hclass : IsClassicalStrictParaSuper Q ψ (ball p.1 r) (p.2 - r ^ 2) p.2 := by
    refine ⟨hψ, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
    · rw [hclosure] at hq
      obtain ⟨⟨hF, -⟩, hφH⟩ := hbounds q hq.2
      rw [hψheat]
      have : -(η * M) ≤ η * (dₜ h₁ q - lapₓ h₁ q) := by
        have := neg_abs_le (dₜ h₁ q - lapₓ h₁ q)
        nlinarith
      linarith
    · rw [hclosure] at hq
      rcases hfr with hpos | hgrad
      · -- `ψ > 0` on the closed cylinder, so `∂{ψ > 0}` misses it
        exfalso
        have hq2 : q.2 ≤ p.2 := (mem_closedParCyl.1 hq.2).2.2
        have hψq : 0 < ψ q := by
          have := bumpP_nonneg hq2
          have := hpos q hq.2
          simp only [hψdef]
          nlinarith
        have hopen : IsOpen {q | 0 < ψ q} := isOpen_lt continuous_const hψ.continuous
        exact hq.1.2 (by rw [hopen.interior_eq]; exact hψq)
      · obtain ⟨⟨-, hG⟩, -⟩ := hbounds q hq.2
        rw [hψgrad]
        calc ‖gradₓ φ q + η • gradₓ h₁ q‖ ≤ ‖gradₓ φ q‖ + η * ‖gradₓ h₁ q‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_smul, Real.norm_of_nonneg hη.le]
          _ ≤ ‖gradₓ φ q‖ + η * M := by gcongr
          _ < Q q.1 := by linarith [hgrad q hq.2]
  -- `u ≺_S ψ` on the parabolic boundary
  have hbdry : PrecOn u ψ S (parBdry (ball p.1 r) (p.2 - r ^ 2) p.2) := by
    rintro q ⟨hqS, hq⟩
    have hqC := parBdry_ball_subset_closedParCyl hr hq
    have hu := hle q ⟨hqS, hsubCyl hqC⟩
    have hb := sq_le_bumpP hr hq
    simp only [hψdef]
    nlinarith
  have hconcl := hsub.2.2.2.2.2 _ _ _ ψ (admissibleCyl_ball hr hsubUI) hclass hbdry
  have hp := hconcl p ⟨hpS, mem_cyl_ball hr⟩
  simp only [hψdef, hh₁def, bumpP_self] at hp
  linarith [hcross.eq]

/-- Relaxed-subsolution bridge. If `(u, E)` is a relaxed subsolution, `Q` is continuous at `x₀`, and
a `C^∞` function `φ` crosses `u` from above in `E` at `p = (x₀, t₀) ∈ U × I` (with `I` containing a
left neighbourhood of `t₀`), then `(∂ₜφ - Δφ)(p) ≤ 0`, or `φ(p) = 0` and `Q(x₀) ≤ |∇φ(p)|`. -/
theorem IsParaRelaxedSub.touching_alt (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) (hQ : ContinuousAt Q p.1) (hφ : ContDiff ℝ ∞ φ)
    (hcross : CrossesFromAbove S u φ p) :
    dₜ φ p - lapₓ φ p ≤ 0 ∨ (φ p = 0 ∧ Q p.1 ≤ ‖gradₓ φ p‖) := by
  by_contra hcon
  simp only [not_or, not_and, not_le] at hcon
  obtain ⟨hH, hfr⟩ := hcon
  have hφp : 0 ≤ φ p := by
    rw [← hcross.eq]
    exact hsub.2.1 p ⟨hpU, mem_of_mem_nhdsWithin self_mem_Iic hpI⟩
  rcases hφp.lt_or_eq with hpos | hzero
  · exact hsub.false_of_crossesFromAbove hU hpU hpI hφ hcross hH (Or.inl hpos)
  · exact hsub.false_of_crossesFromAbove hU hpU hpI hφ hcross hH
      (Or.inr ⟨hQ, hfr hzero.symm⟩)

/-- Relaxed-subsolution bridge at a positive contact value: no hypothesis on `Q`. -/
theorem IsParaRelaxedSub.heat_nonpos_of_pos (hsub : IsParaRelaxedSub U Q I u S) (hU : IsOpen U)
    (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) (hφ : ContDiff ℝ ∞ φ)
    (hcross : CrossesFromAbove S u φ p) (hpos : 0 < u p) : dₜ φ p - lapₓ φ p ≤ 0 := by
  by_contra hH
  exact hsub.false_of_crossesFromAbove hU hpU hpI hφ hcross (not_le.1 hH)
    (Or.inl (hcross.eq ▸ hpos))

end Sub

/-! ### Supersolutions -/

section Super

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {v : E d × ℝ → ℝ}
  {φ : E d × ℝ → ℝ} {p : E d × ℝ}

/-- Core of the supersolution bridge: if `φ` crosses `v` from below in `U × I` at `p`, the heat
operator of `φ` at `p` cannot be negative while `φ(p) > 0` or `|∇φ(p)| > Q(x₀)` (the latter with
`Q` continuous at `x₀`).

The perturbed test function is `ψ = φ - η h₁ + c`. The barrier clause for supersolutions
is `Prec ψ v univ F`, i.e. `ψ < v` on `closure {ψ > 0} ∩ F`. We check the boundary hypothesis in the
stronger form `ψ < v` on all of `∂ₚ` (so the `closure {ψ > 0}` restriction is not needed), and at
the conclusion we check that `p ∈ closure {ψ > 0}`, since `ψ(p) = v(p) + c > 0`. -/
theorem IsParaSuper.false_of_crossesFromBelow (hsup : IsParaSuper U Q I v)
    (hU : IsOpen U) (hpU : p.1 ∈ U) (hpI : I ∈ 𝓝[≤] p.2) (hφ : ContDiff ℝ ∞ φ)
    (hcross : CrossesFromBelow (U ×ˢ I) v φ p) (hH : dₜ φ p - lapₓ φ p < 0)
    (hfront : 0 < φ p ∨ (ContinuousAt Q p.1 ∧ Q p.1 < ‖gradₓ φ p‖)) : False := by
  set H := -(dₜ φ p - lapₓ φ p) with hHdef
  have hH' : 0 < H := by linarith
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  set h₁ := bumpP p with hh₁def
  have hh₁ : ContDiff ℝ ∞ h₁ := contDiff_bumpP p
  have hh₁2 : ContDiff ℝ 2 h₁ := contDiff_bumpP p
  have hh₁d : Differentiable ℝ h₁ := (contDiff_bumpP p (n := 1)).differentiable one_ne_zero
  obtain ⟨M, hM0, hMev⟩ := exists_bound_bumpP p
  have hHev : ∀ᶠ q in 𝓝 p, dₜ φ q - lapₓ φ q < -(H / 2) :=
    (show Continuous fun q ↦ dₜ φ q - lapₓ φ q from
      (continuous_dₜ hφ1).sub (continuous_lapₓ hφ2)).continuousAt.eventually_lt continuousAt_const
      (by linarith)
  obtain ⟨g, hg, hgev⟩ : ∃ g > 0, (∀ᶠ q in 𝓝 p, 2 * g < φ q) ∨
      (∀ᶠ q in 𝓝 p, Q q.1 + 2 * g < ‖gradₓ φ q‖) := by
    rcases hfront with hpos | ⟨hQ, hgrad⟩
    · refine ⟨φ p / 4, by positivity, Or.inl ?_⟩
      exact continuousAt_const.eventually_lt hφ.continuous.continuousAt (by linarith)
    · refine ⟨(‖gradₓ φ p‖ - Q p.1) / 4, by linarith, Or.inr ?_⟩
      exact ((hQ.comp continuousAt_fst).add continuousAt_const).eventually_lt
        (continuous_gradₓ hφ1).norm.continuousAt
        (by simp only [Pi.add_apply, Function.comp_apply]; linarith)
  obtain ⟨η, hη, hηM⟩ := exists_eta hM0 (lt_min (half_pos hH') hg)
  have hηH : η * M < H / 2 := hηM.trans_le (min_le_left _ _)
  have hηg : η * M < g := hηM.trans_le (min_le_right _ _)
  have hpUI : p ∈ U ×ˢ I := hcross.1
  obtain ⟨r₀, hr₀pos, hle⟩ := hcross.2.2
  have hrev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ closedParCyl p.1 p.2 r ⊆ U ×ˢ I ∧
      closedParCyl p.1 p.2 r ⊆ parCyl p.1 p.2 r₀ ∧ η * r ^ 2 < g ∧
      (∀ q ∈ closedParCyl p.1 p.2 r, (|dₜ h₁ q - lapₓ h₁ q| ≤ M ∧ ‖gradₓ h₁ q‖ ≤ M) ∧
        dₜ φ q - lapₓ φ q < -(H / 2)) ∧
      ((∀ q ∈ closedParCyl p.1 p.2 r, 2 * g < φ q) ∨
        (∀ q ∈ closedParCyl p.1 p.2 r, Q q.1 + 2 * g < ‖gradₓ φ q‖)) := by
    have hfr : ∀ᶠ r in 𝓝[>] (0 : ℝ), ((∀ q ∈ closedParCyl p.1 p.2 r, 2 * g < φ q) ∨
        (∀ q ∈ closedParCyl p.1 p.2 r, Q q.1 + 2 * g < ‖gradₓ φ q‖)) := by
      rcases hgev with h | h
      · exact (eventually_forall_closedParCyl h).mono fun r hr ↦ Or.inl hr
      · exact (eventually_forall_closedParCyl h).mono fun r hr ↦ Or.inr hr
    filter_upwards [self_mem_nhdsWithin, eventually_closedParCyl_subset_prod hU hpU hpI,
      eventually_closedParCyl_subset_parCyl hr₀pos, eventually_mul_sq_lt η hg,
      eventually_forall_closedParCyl (hMev.and hHev), hfr] with r h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨r, hr, hsubUI, hsubCyl, hηr, hbounds, hfr⟩ := hrev.exists
  set c := η * r ^ 2 / 2 with hcdef
  have hc : 0 < c := by positivity
  set ψ : E d × ℝ → ℝ := fun q ↦ φ q + (-η * h₁ q + c) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := hφ.add ((contDiff_const.mul hh₁).add contDiff_const)
  have hψheat : ∀ q, dₜ ψ q - lapₓ ψ q = (dₜ φ q - lapₓ φ q) + -η * (dₜ h₁ q - lapₓ h₁ q) :=
    dₜ_sub_lapₓ_add_mul_add hφ2 hh₁2 (-η) c
  have hψgrad : ∀ q, gradₓ ψ q = gradₓ φ q + (-η) • gradₓ h₁ q :=
    gradₓ_add_mul_add hφd hh₁d (-η) c
  have hclosure : closure (ball p.1 r) ×ˢ Icc (p.2 - r ^ 2) p.2 = closedParCyl p.1 p.2 r := by
    rw [closure_ball _ hr.ne']; rfl
  -- `ψ` is a classical strict subsolution on the closed cylinder
  have hclass : IsClassicalStrictParaSub Q ψ (ball p.1 r) (p.2 - r ^ 2) p.2 := by
    refine ⟨hψ, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
    · rw [hclosure] at hq
      obtain ⟨⟨hF, -⟩, hφH⟩ := hbounds q hq.2
      rw [hψheat]
      have : -η * (dₜ h₁ q - lapₓ h₁ q) ≤ η * M := by
        have := le_abs_self (-(dₜ h₁ q - lapₓ h₁ q))
        rw [abs_neg] at this
        nlinarith
      linarith
    · rw [hclosure] at hq
      rcases hfr with hpos | hgrad
      · -- `ψ > 0` on the closed cylinder, so `∂{ψ > 0}` misses it
        exfalso
        have hψq : 0 < ψ q := by
          have := bumpP_le hq.2
          have := hpos q hq.2
          simp only [hψdef]
          nlinarith
        have hopen : IsOpen {q | 0 < ψ q} := isOpen_lt continuous_const hψ.continuous
        exact hq.1.2 (by rw [hopen.interior_eq]; exact hψq)
      · obtain ⟨⟨-, hG⟩, -⟩ := hbounds q hq.2
        rw [hψgrad]
        have hn : ‖(-η) • gradₓ h₁ q‖ ≤ η * M := by
          rw [norm_smul, norm_neg, Real.norm_of_nonneg hη.le]
          gcongr
        have := norm_sub_norm_le (gradₓ φ q) (-((-η) • gradₓ h₁ q))
        rw [sub_neg_eq_add, norm_neg] at this
        linarith [hgrad q hq.2]
  -- `ψ ≺ v` on the parabolic boundary, in the stronger form `ψ < v` on all of `∂ₚ`
  have hbdry : Prec ψ v univ (parBdry (ball p.1 r) (p.2 - r ^ 2) p.2) := by
    rintro q ⟨-, hq⟩
    have hqC := parBdry_ball_subset_closedParCyl hr hq
    have hv := hle q ⟨hsubUI hqC, hsubCyl hqC⟩
    have hb := sq_le_bumpP hr hq
    simp only [hψdef]
    nlinarith
  have hconcl := hsup.2.2 _ _ _ ψ (admissibleCyl_ball hr hsubUI) hclass hbdry
  -- `p ∈ closure {ψ > 0}` since `ψ(p) = v(p) + c > 0`
  have hψp : ψ p = v p + c := by
    simp only [hψdef, hh₁def, bumpP_self, hcross.eq]; ring
  have hvp : 0 ≤ v p := hsup.2.1 p hpUI
  have hpcl : p ∈ closure (posSetP ψ univ) :=
    subset_closure ⟨mem_univ _, by rw [hψp]; linarith⟩
  have hp := hconcl p ⟨hpcl, mem_cyl_ball hr⟩
  linarith

/-- Supersolution bridge. If `v` is a supersolution, `Q` is continuous at `x₀`, and a `C^∞` function
`φ` crosses `v` from below in `U × I` at `p = (x₀, t₀)` (with `U` open and `I` containing a left
neighbourhood of `t₀`), then `(∂ₜφ - Δφ)(p) ≥ 0`, or `φ(p) = 0` and `|∇φ(p)| ≤ Q(x₀)`. -/
theorem IsParaSuper.touching_alt (hsup : IsParaSuper U Q I v) (hU : IsOpen U)
    (hpI : I ∈ 𝓝[≤] p.2) (hQ : ContinuousAt Q p.1) (hφ : ContDiff ℝ ∞ φ)
    (hcross : CrossesFromBelow (U ×ˢ I) v φ p) :
    0 ≤ dₜ φ p - lapₓ φ p ∨ (φ p = 0 ∧ ‖gradₓ φ p‖ ≤ Q p.1) := by
  by_contra hcon
  simp only [not_or, not_and, not_le] at hcon
  obtain ⟨hH, hfr⟩ := hcon
  have hφp : 0 ≤ φ p := by rw [← hcross.eq]; exact hsup.2.1 p hcross.1
  rcases hφp.lt_or_eq with hpos | hzero
  · exact hsup.false_of_crossesFromBelow hU hcross.1.1 hpI hφ hcross hH (Or.inl hpos)
  · exact hsup.false_of_crossesFromBelow hU hcross.1.1 hpI hφ hcross hH
      (Or.inr ⟨hQ, hfr hzero.symm⟩)

/-- Supersolution bridge at a positive contact value: no hypothesis on `Q`. -/
theorem IsParaSuper.heat_nonneg_of_pos (hsup : IsParaSuper U Q I v) (hU : IsOpen U)
    (hpI : I ∈ 𝓝[≤] p.2) (hφ : ContDiff ℝ ∞ φ) (hcross : CrossesFromBelow (U ×ˢ I) v φ p)
    (hpos : 0 < v p) : 0 ≤ dₜ φ p - lapₓ φ p := by
  by_contra hH
  exact hsup.false_of_crossesFromBelow hU hcross.1.1 hpI hφ hcross (not_le.1 hH)
    (Or.inl (hcross.eq ▸ hpos))

end Super

end BernoulliComparison
