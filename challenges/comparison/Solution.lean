module

public import BernoulliComparison

@[expose] public section

/-!
# Solution: comparison for the parabolic Bernoulli problem

Discharges the two comparison statements through the library theorems
`BernoulliComparison.para_relaxed_comparison` and `BernoulliComparison.para_strict_comparison`.

`challenge_model_sanity` is proved directly. The explicit barriers are written as the library's
caloric paraboloid `Barriers.paraboloid` plus a multiple of `t`, so that the heat operator and the
spatial gradient come from `Barriers.dₜ_sub_lapₓ_paraboloid`, `Barriers.gradₓ_paraboloid` and the
linearity lemmas of `Touching/Calculus.lean`. The positive constant is handled by a classical
maximum principle on the closed cylinder.
-/

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

theorem challenge_relaxed_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T) :=
  para_relaxed_comparison hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec

theorem challenge_strict_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaSub U Q (Ioc 0 T) u) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    {N : Set (E d × ℝ)} (hN : N ∈ 𝓝ˢ (parBdry U 0 T))
    (hprec : Prec u v (closure U ×ˢ Icc 0 T) N) :
    Prec u v (closure U ×ˢ Icc 0 T) (closure U ×ˢ Icc 0 T) :=
  para_strict_comparison hU hUb hQ hQpos hT hu hv hsub hsuper hN hprec

/-- The paraboloid plus `η t`: its heat operator is `η`. -/
private theorem heat_paraboloid_add (x₀ : E d) (t₁ ρ κ η : ℝ) (q : E d × ℝ) :
    dₜ (fun q ↦ Barriers.paraboloid x₀ t₁ ρ κ q + (η * (q.2 - 0) + 0)) q -
      lapₓ (fun q ↦ Barriers.paraboloid x₀ t₁ ρ κ q + (η * (q.2 - 0) + 0)) q = η := by
  have h := dₜ_sub_lapₓ_add_mul_add (Barriers.contDiff_paraboloid x₀ t₁ ρ κ)
    (h := fun q : E d × ℝ ↦ q.2 - 0) (contDiff_snd.sub contDiff_const) η 0 q
  rw [h, Barriers.dₜ_sub_lapₓ_paraboloid, dₜ_time_sub, lapₓ_time_sub]
  ring

private theorem contDiff_paraboloid_add (x₀ : E d) (t₁ ρ κ η : ℝ) :
    ContDiff ℝ ∞ (fun q ↦ Barriers.paraboloid x₀ t₁ ρ κ q + (η * (q.2 - 0) + 0)) :=
  (Barriers.contDiff_paraboloid x₀ t₁ ρ κ).add
    ((contDiff_const.mul (contDiff_snd.sub contDiff_const)).add contDiff_const)

/-- A point of the frontier of `{φ > 0}` is a zero of `φ`, for continuous `φ`. -/
private theorem eq_zero_of_mem_frontier {φ : E d × ℝ → ℝ} (hφ : Continuous φ) {p : E d × ℝ}
    (hp : p ∈ frontier {q | 0 < φ q}) : φ p = 0 := by
  rw [(isOpen_lt continuous_const hφ).frontier_eq] at hp
  exact le_antisymm (not_lt.1 hp.2) (closure_lt_subset_le continuous_const hφ hp.1)

/-- The explicit barrier `1 + t - |x|²`, as a paraboloid plus a multiple of `t`. -/
private theorem barrier_eq :
    (fun p : E d × ℝ ↦ 1 + p.2 - ‖p.1‖ ^ 2) =
      fun q ↦ Barriers.paraboloid 0 0 1 1 q + ((2 * d + 1) * (q.2 - 0) + 0) := by
  funext q
  simp only [Barriers.paraboloid_apply, sub_zero]
  ring

private theorem barrier_super :
    IsClassicalStrictParaSuper (fun _ ↦ 3) (fun p : E d × ℝ ↦ 1 + p.2 - ‖p.1‖ ^ 2)
      (ball 0 2) 0 1 := by
  have hφ := contDiff_paraboloid_add (0 : E d) 0 1 1 (2 * d + 1)
  rw [barrier_eq]
  refine ⟨hφ, fun p _ ↦ ?_, fun p hp ↦ ?_⟩
  · rw [heat_paraboloid_add]; positivity
  · have h0 := eq_zero_of_mem_frontier hφ.continuous hp.1
    have hgrad := gradₓ_add_mul_add
      ((Barriers.contDiff_paraboloid (n := 1) (0 : E d) 0 1 1).differentiable one_ne_zero)
      (h := fun q : E d × ℝ ↦ q.2 - 0) (differentiable_snd.sub_const 0) (2 * d + 1) 0 p
    rw [hgrad, Barriers.gradₓ_paraboloid, gradₓ_time_sub, smul_zero, add_zero, norm_smul,
      sub_zero]
    simp only [Barriers.paraboloid_apply, sub_zero] at h0
    have ht := hp.2.2.2
    have hn := norm_nonneg p.1
    norm_num at h0 ⊢
    nlinarith

private theorem barrier_frontier_nonempty (hd : 0 < d) :
    (frontier {p : E d × ℝ | 0 < 1 + p.2 - ‖p.1‖ ^ 2} ∩
      (closure (ball (0 : E d) 2) ×ˢ Icc 0 1)).Nonempty := by
  set x₀ : E d := EuclideanSpace.single ⟨0, hd⟩ 1
  have hx₀ : ‖x₀‖ = 1 := by simp [x₀]
  have hcont : Continuous fun p : E d × ℝ ↦ 1 + p.2 - ‖p.1‖ ^ 2 := by fun_prop
  refine ⟨(x₀, 0), ?_, subset_closure (by simp [hx₀]), by simp⟩
  rw [(isOpen_lt continuous_const hcont).frontier_eq]
  refine ⟨?_, by simp [hx₀]⟩
  have ht : Tendsto (fun s : ℝ ↦ (x₀, s)) (𝓝[>] 0) (𝓝 (x₀, 0)) :=
    ((continuous_const.prodMk continuous_id).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp [hx₀, mem_Ioi.1 hs]

/-- The explicit subsolution barrier `1 - |x|² - (2d + 1)t`, as a paraboloid minus `t`. -/
private theorem sub_barrier_eq :
    (fun p : E d × ℝ ↦ 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2) =
      fun q ↦ Barriers.paraboloid 0 0 1 1 q + ((-1) * (q.2 - 0) + 0) := by
  funext q
  simp only [Barriers.paraboloid_apply, sub_zero]
  ring

private theorem barrier_sub :
    IsClassicalStrictParaSub (fun _ ↦ 1) (fun p : E d × ℝ ↦ 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2)
      (ball 0 2) 0 (1 / (4 * d + 2)) := by
  have hφ := contDiff_paraboloid_add (0 : E d) 0 1 1 (-1)
  rw [sub_barrier_eq]
  refine ⟨hφ, fun p _ ↦ ?_, fun p hp ↦ ?_⟩
  · rw [heat_paraboloid_add]; norm_num
  · have h0 := eq_zero_of_mem_frontier hφ.continuous hp.1
    have hgrad := gradₓ_add_mul_add
      ((Barriers.contDiff_paraboloid (n := 1) (0 : E d) 0 1 1).differentiable one_ne_zero)
      (h := fun q : E d × ℝ ↦ q.2 - 0) (differentiable_snd.sub_const 0) (-1) 0 p
    rw [hgrad, Barriers.gradₓ_paraboloid, gradₓ_time_sub, smul_zero, add_zero, norm_smul,
      sub_zero]
    simp only [Barriers.paraboloid_apply, sub_zero] at h0
    -- up to `T_d = 1/(4d + 2)` the ball has `|x|² = 1 - (2d + 1)t ≥ 1/2`
    have ht : p.2 * (4 * d + 2) ≤ 1 := (le_div_iff₀ (by positivity)).1 hp.2.2.2
    have hn := norm_nonneg p.1
    norm_num at h0 ⊢
    nlinarith

private theorem sub_barrier_frontier_nonempty (hd : 0 < d) :
    (frontier {p : E d × ℝ | 0 < 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2} ∩
      (closure (ball (0 : E d) 2) ×ˢ Icc (0 : ℝ) (1 / (4 * d + 2)))).Nonempty := by
  set x₀ : E d := EuclideanSpace.single ⟨0, hd⟩ 1
  have hx₀ : ‖x₀‖ = 1 := by simp [x₀]
  have hcont : Continuous fun p : E d × ℝ ↦ 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2 := by fun_prop
  refine ⟨(x₀, 0), ?_, subset_closure (by simp [hx₀]), le_rfl, by positivity⟩
  rw [(isOpen_lt continuous_const hcont).frontier_eq]
  refine ⟨?_, by simp [hx₀]⟩
  have ht : Tendsto (fun s : ℝ ↦ (x₀, s)) (𝓝[<] 0) (𝓝 (x₀, 0)) :=
    ((continuous_const.prodMk continuous_id).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < (2 * (d : ℝ) + 1) * -s := mul_pos (by positivity) (neg_pos.2 hs)
  show 0 < 1 - ‖x₀‖ ^ 2 - (2 * (d : ℝ) + 1) * s
  rw [hx₀]
  linarith

/-- A positive constant is a supersolution: a strict subsolution `φ` attains its maximum over the
closed cylinder; at a point of the parabolic boundary the boundary ordering excludes `φ ≥ c`, and
at an interior point `∂ₜφ ≥ 0 ≥ Δφ` contradicts `∂ₜφ - Δφ < 0`. -/
private theorem const_super (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) {c : ℝ} (hc : 0 < c) :
    IsParaSuper U Q I (fun _ ↦ c) := by
  refine ⟨continuousOn_const, fun _ _ ↦ hc.le, fun V a b φ hVab hφ hbd p hp ↦ ?_⟩
  obtain ⟨hVo, hVb, hab, -⟩ := hVab
  have hpD : p ∈ closure V ×ˢ Icc a b :=
    ⟨subset_closure hp.2.1, Ioc_subset_Icc_self hp.2.2⟩
  obtain ⟨q, hqD, hmax⟩ := (hVb.isCompact_closure.prod isCompact_Icc).exists_isMaxOn
    ⟨p, hpD⟩ hφ.1.continuous.continuousOn
  by_contra hcp
  have hq : c ≤ φ q := (not_lt.1 hcp).trans (hmax hpD)
  have hqcl : q ∈ closure (posSetP φ univ) := subset_closure ⟨mem_univ _, hc.trans_le hq⟩
  -- `q` is not on the parabolic boundary
  have hq1 : q.1 ∈ V := by
    by_contra h
    exact (hbd q ⟨hqcl, Or.inr ⟨⟨hqD.1, by rwa [hVo.interior_eq]⟩, hqD.2⟩⟩).not_ge hq
  have hq2 : a < q.2 :=
    lt_of_le_of_ne hqD.2.1 fun h ↦ (hbd q ⟨hqcl, Or.inl ⟨hqD.1, h.symm⟩⟩).not_ge hq
  have hheat := hφ.2.1 q ⟨closure_mono (fun r hr ↦ hr.2) hqcl, hqD⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  -- second-order conditions at the maximum, applied to `-φ`
  have h1 : 0 ≤ lapₓ (fun r ↦ -1 * φ r) q := by
    refine lapₓ_nonneg_of_isLocalMin (contDiff_const.mul hφ2) ?_
    filter_upwards [hVo.mem_nhds hq1] with y hy
    have : φ (y, q.2) ≤ φ q := hmax ⟨subset_closure hy, hqD.2⟩
    show -1 * φ q ≤ -1 * φ (y, q.2)
    linarith
  have h2 : dₜ (fun r ↦ -1 * φ r) q ≤ 0 := by
    refine dₜ_nonpos_of_isLocalMinOn_Iic ((contDiff_const.mul hφ2).differentiable two_ne_zero) ?_
    filter_upwards [Ioc_mem_nhdsLE hq2] with s hs
    have : φ (q.1, s) ≤ φ q := hmax ⟨hqD.1, hs.1.le, hs.2.trans hqD.2.2⟩
    show -1 * φ q ≤ -1 * φ (q.1, s)
    linarith
  rw [lapₓ_const_mul hφ2] at h1
  rw [dₜ_const_mul (hφ2.differentiable two_ne_zero)] at h2
  linarith

private theorem zero_relaxedSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) :
    IsParaRelaxedSub U Q I (fun _ ↦ 0) ∅ :=
  ⟨continuousOn_const, fun _ _ ↦ le_rfl, isClosed_empty, empty_subset _,
    fun _ hp ↦ (lt_irrefl _ hp.2).elim, fun _ _ _ _ _ _ _ _ hp ↦ hp.1.elim⟩

/-- `1 - t/2` is not a supersolution: with `m = 1/(4(d+1))²`, the barrier
`φ = 1 - t/2 - m/2 + 2m(t - 1/2) - m|x|²` is a positive strict subsolution on
`B̄₁(0) × [1/2, 1]`, lies below `v` on the parabolic boundary, and exceeds it at `(0, 1)`. -/
private theorem decreasing_not_super (Q : E d → ℝ) :
    ¬ IsParaSuper (ball (0 : E d) 2) Q (Ioc 0 1) (fun p ↦ 1 - p.2 / 2) := by
  rintro ⟨-, -, hR⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 4 * (d + 1) := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = 1 / ρ ^ 2 := ⟨_, rfl⟩
  have hd0 : (0 : ℝ) ≤ d := d.cast_nonneg
  have hρ4 : 4 ≤ ρ := by rw [hρ]; linarith
  have hm : 0 < m := by
    have : 0 < ρ := by linarith
    rw [hm_def]; positivity
  have hm16 : m ≤ 1 / 16 := by
    rw [hm_def, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hdm : 2 * (d + 1) * m ≤ 1 / 8 := by
    have hρm : m * ρ ^ 2 = 1 := by rw [hm_def]; field_simp
    rw [hρ] at hρm
    nlinarith [mul_nonneg (mul_nonneg hd0 hd0) hm.le, mul_nonneg hd0 hm.le]
  obtain ⟨φ, hφ_def⟩ : ∃ φ : E d × ℝ → ℝ, φ = fun q ↦ Barriers.paraboloid 0 (1 / 2) ρ
      (1 - 3 * m / 2 - d * m) q + ((-1 / 2 + 2 * m + 2 * d * m) * (q.2 - 0) + 0) := ⟨_, rfl⟩
  have hφq : ∀ q : E d × ℝ,
      φ q = 1 - q.2 / 2 - m / 2 + 2 * m * (q.2 - 1 / 2) - m * ‖q.1‖ ^ 2 := by
    intro q
    have hρ0 : ρ ≠ 0 := by linarith
    simp only [hφ_def, Barriers.paraboloid_apply, hm_def, sub_zero]
    field_simp
    ring
  have hφc : ContDiff ℝ ∞ φ := hφ_def ▸ contDiff_paraboloid_add _ _ _ _ _
  have hφpos : ∀ q ∈ closedBall (0 : E d) 1 ×ˢ Icc (1 / 2 : ℝ) 1, 0 < φ q := by
    rintro q ⟨hx, ht⟩
    have hx' : ‖q.1‖ ≤ 1 := by simpa using hx
    have := ht.1
    have := ht.2
    rw [hφq]
    nlinarith [norm_nonneg q.1]
  have hcl : closure (ball (0 : E d) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hbar : IsClassicalStrictParaSub Q φ (ball 0 1) (1 / 2) 1 := by
    refine ⟨hφc, fun q _ ↦ ?_, fun q hq ↦ ?_⟩
    · rw [hφ_def, heat_paraboloid_add]; linarith
    · rw [hcl] at hq
      exact absurd (eq_zero_of_mem_frontier hφc.continuous hq.1) (hφpos q hq.2).ne'
  have hadm : AdmissibleCyl (ball (0 : E d) 2) (Ioc 0 1) (ball 0 1) (1 / 2) 1 := by
    refine ⟨isOpen_ball, isBounded_ball, by norm_num, ?_⟩
    rintro q ⟨hx, ht⟩
    rw [hcl] at hx
    exact ⟨closedBall_subset_ball (by norm_num) hx, lt_of_lt_of_le (by norm_num) ht.1, ht.2⟩
  have hbd : Prec φ (fun p : E d × ℝ ↦ 1 - p.2 / 2) univ (parBdry (ball 0 1) (1 / 2) 1) := by
    rintro q ⟨-, hq⟩
    show φ q < 1 - q.2 / 2
    rw [hφq]
    rcases hq with ⟨-, ht⟩ | ⟨hx, ht⟩
    · rw [mem_singleton_iff.1 ht]
      nlinarith [norm_nonneg q.1]
    · rw [frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hx
      rw [hx]
      nlinarith [ht.2]
  have hq0 : ((0 : E d), (1 : ℝ)) ∈ closedBall (0 : E d) 1 ×ˢ Icc (1 / 2 : ℝ) 1 :=
    ⟨by simp, by norm_num, le_rfl⟩
  have h := hR _ _ _ φ hadm hbar hbd ((0 : E d), 1)
    ⟨subset_closure ⟨mem_univ _, hφpos _ hq0⟩, by simp, by norm_num, le_rfl⟩
  have h' : φ ((0 : E d), 1) < 1 - 1 / 2 := h
  rw [hφq] at h'
  norm_num at h'
  linarith

theorem challenge_model_sanity (d : ℕ) :
    IsClassicalStrictParaSuper (fun _ ↦ 3) (fun p : E d × ℝ ↦ 1 + p.2 - ‖p.1‖ ^ 2)
        (ball 0 2) 0 1 ∧
      (0 < d → (frontier {p : E d × ℝ | 0 < 1 + p.2 - ‖p.1‖ ^ 2} ∩
        (closure (ball (0 : E d) 2) ×ˢ Icc 0 1)).Nonempty) ∧
      IsClassicalStrictParaSub (fun _ ↦ 1)
        (fun p : E d × ℝ ↦ 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2) (ball 0 2) 0 (1 / (4 * d + 2)) ∧
      (0 < d → (frontier {p : E d × ℝ | 0 < 1 - ‖p.1‖ ^ 2 - (2 * d + 1) * p.2} ∩
        (closure (ball (0 : E d) 2) ×ˢ Icc (0 : ℝ) (1 / (4 * d + 2)))).Nonempty) ∧
      (∀ (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (c : ℝ), 0 < c →
        IsParaSuper U Q I (fun _ ↦ c)) ∧
      (∀ (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ), IsParaRelaxedSub U Q I (fun _ ↦ 0) ∅) ∧
      ∀ Q : E d → ℝ, ¬ IsParaSuper (ball (0 : E d) 2) Q (Ioc 0 1) (fun p ↦ 1 - p.2 / 2) :=
  ⟨barrier_super, barrier_frontier_nonempty, barrier_sub, sub_barrier_frontier_nonempty,
    fun U Q I _ hc ↦ const_super U Q I hc,
    zero_relaxedSub, decreasing_not_super⟩

end BernoulliComparison
