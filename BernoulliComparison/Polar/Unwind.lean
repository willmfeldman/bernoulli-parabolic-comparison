/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Polar.Sausage
public import BernoulliComparison.Contact.BumpPositivity

/-!
# Unwinding the first convolution at the poles

The first convolution step is by the flat disk `K₀ = D̄_{λ₁} × {0}`. Unwinding it transfers
information about the convolved functions at the contact point to the raw pair `(û, E)` and the
raw supersolution `v̂` on the sausage `𝒮` and the top disk `𝒟` (`Polar/Sausage.lean`).

* `unwind_u`: the raw pair `(û, E)` has `E ∩ 𝒮 = E ∩ 𝒟 = ∅`, `û = 0` on `𝒮 ∪ 𝒟̄`, and, if
  `ν¹ = e_t`, a rim witness `w₁ = (x̄, t⋆) ∈ E` with `|x̄ - x⋆| = λ₁`;
* `unwind_v`: the raw supersolution has `v̂ > 0` on `𝒮 ∪ 𝒟` and, if `ν² = e_t`, a rim zero
  `p₂ = (x̄, t⋆)`, `v̂(p₂) = 0`, `|x̄ - x⋆| = λ₁`.

The individual statements about `𝒮` and `𝒟` do not use the polar hypothesis, and are stated
without it. The rim points are given as `x̄` with `|x̄ - x⋆| = λ₁`.

In the proof that `v̂ > 0` on `𝒟` (`vhat_pos_of_mem_topDisk`) the bump height is
`t⋆ - t₁ = r²/(4d + 4)`, so that `t₁ < t⋆` also when `d = 0`; only `4d (t⋆ - t₁) ≤ r²` is used.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Polar

open Crossing Config Contact

variable {d : ℕ}

/-- A point is in the closure of `S` if its backward time translates `(x, t - ε)`,
`0 < ε < δ`, lie in `S`. -/
theorem mem_closure_of_forall_sub {S : Set (E d × ℝ)} {q : E d × ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ ε ∈ Ioo 0 δ, ((q.1, q.2 - ε) : E d × ℝ) ∈ S) : q ∈ closure S := by
  have hc : Continuous fun ε : ℝ ↦ ((q.1, q.2 - ε) : E d × ℝ) := by fun_prop
  have ht : Tendsto (fun ε : ℝ ↦ ((q.1, q.2 - ε) : E d × ℝ)) (𝓝[>] 0) (𝓝 q) := by
    have h0 := hc.tendsto 0
    simp only [sub_zero, Prod.mk.eta] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto ht (Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ) h)

variable {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset} (C : ContactData P)

/-- `k ∈ K₀ = D̄_{λ₁}` iff `|k.1| ≤ λ₁` and `k.2 = 0`. -/
theorem mem_K₀_iff {k : E d × ℝ} : k ∈ P.K₀ ↔ ‖k.1‖ ≤ P.ℓ ∧ k.2 = 0 := by
  simp [Config.K₀, mem_spDisk]

/-- Translates of `U₀ × (0, T]` by `K₀` lie in `D`. -/
theorem add_mem_D_of_mem_K₀ {p k : E d × ℝ} (hp : p ∈ P.U₀ ×ˢ Ioc 0 T) (hk : k ∈ P.K₀) :
    p + k ∈ P.D := by
  rw [mem_K₀_iff] at hk
  refine ⟨subset_closure (P.add_mem_U_of_mem_U₀ hp.1 hk.1), ?_⟩
  simp only [Prod.snd_add, hk.2, add_zero]
  exact ⟨hp.2.1.le, hp.2.2⟩

/-- Points of `B_μ(p̂)` lie in `U₀ × (0, T]`. -/
theorem mem_U₀_prod_of_mem_dualBallOpen {p : E d × ℝ} (hp : p ∈ stBallOpen C.phat P.μ) :
    p ∈ P.U₀ ×ˢ Ioc 0 T := by
  have h := (C.dualBallOpen_subset_past hp).1
  exact ⟨P.U₁_subset_U₀ h.1, lt_trans (by linarith [P.μ_pos]) h.2.1, h.2.2⟩

/-- `p⋆ ∈ U₀ × (0, T]`. -/
theorem pstar_mem_U₀_prod : C.pstar ∈ P.U₀ ×ˢ Ioc 0 T :=
  ⟨P.U₁_subset_U₀ C.xstar_mem_U₁, by
    change 0 < C.tstar; linarith [C.two_μ_lt_tstar, P.μ_pos], C.tstar_le_T⟩

/-- The decomposition `q = (q.1 - e, q.2) + (e, 0)`. -/
theorem decomp_add (q : E d × ℝ) (e : E d) : ((q.1 - e, q.2) : E d × ℝ) + (e, 0) = q := by
  ext <;> simp

/-! ### Unwinding for the subsolution -/

/-- `E ∩ 𝒮 = ∅`. -/
theorem not_mem_of_mem_sausage {q : E d × ℝ} (hq : q ∈ sausage C) : q ∉ Eset := by
  obtain ⟨e, he, hp⟩ := sausage_decomp C hq
  intro hqE
  refine C.dual_not_mem_E₀ _ hp ⟨prod_Ioc_subset_D₀ P (mem_U₀_prod_of_mem_dualBallOpen C hp),
    ((e, 0) : E d × ℝ), mem_K₀_iff.2 ⟨he, rfl⟩, ?_⟩
  rwa [decomp_add]

/-- `û = 0` on `𝒮`. -/
theorem uhat_eq_zero_of_mem_sausage {q : E d × ℝ} (hq : q ∈ sausage C) : P.uhat q = 0 := by
  have hD := mem_D_of_mem_sausage C hq
  refine le_antisymm ?_ (P.uhat_nonneg hD)
  by_contra hpos
  exact not_mem_of_mem_sausage C hq (P.mem_Eset_of_uhat_pos hD (lt_of_not_ge hpos))

/-- `E ∩ 𝒟 = ∅`: a point of `E` in `𝒟` would have points of `E` just below it in time (no
instant creation), and these would lie in `𝒮`. -/
theorem not_mem_of_mem_topDisk {q : E d × ℝ} (hq : q ∈ topDisk C) : q ∉ Eset := by
  intro hqE
  obtain ⟨hq1, hq2⟩ := hq
  rw [mem_ball, dist_eq_norm] at hq1
  rw [mem_singleton_iff] at hq2
  have hqU : q ∈ U ×ˢ Ioc 0 T :=
    mem_prod_of_near C (hq1.trans P.ℓ_lt_lam) (by linarith [P.μ_pos]) hq2.le
  set ε := min (P.ℓ - ‖q.1 - C.xstar‖) P.μ with hε
  have hε0 : 0 < ε := lt_min (by linarith) P.μ_pos
  obtain ⟨r, hrE, hrt, hrd⟩ := P.past_points_hat hqE hqU hε0
  have h1 : ‖r.1 - q.1‖ < ε := by
    have : ‖r.1 - q.1‖ ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg (r.2 - q.2)]
    exact lt_of_abs_lt (abs_lt_of_sq_lt_sq this hε0.le)
  have h2 : |r.2 - q.2| < ε := by
    have : (r.2 - q.2) ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg ‖r.1 - q.1‖]
    exact abs_lt_of_sq_lt_sq this hε0.le
  have hε1 : ε ≤ P.ℓ - ‖q.1 - C.xstar‖ := min_le_left _ _
  have hε2 : ε ≤ P.μ := min_le_right _ _
  have hr1 : ‖r.1 - C.xstar‖ ≤ P.ℓ := by
    have := norm_sub_le_norm_sub_add_norm_sub r.1 q.1 C.xstar
    linarith
  have h2' := abs_lt.1 h2
  refine not_mem_of_mem_sausage C (mem_sausage_of_le C hr1 ?_ ?_) hrE
  · change 0 < C.tstar - r.2; linarith
  · change C.tstar - r.2 < 2 * P.μ; linarith [P.μ_pos]

/-- `û = 0` on `𝒟̄ = B̄_{λ₁}(x⋆) × {t⋆}` (by continuity from `𝒮`). -/
theorem uhat_eq_zero_of_norm_le {x : E d} (hx : ‖x - C.xstar‖ ≤ P.ℓ) :
    P.uhat (x, C.tstar) = 0 := by
  have hS : IsClosed (P.D ∩ P.uhat ⁻¹' {0}) :=
    P.continuousOn_uhat.preimage_isClosed_of_isClosed P.isCompact_D.isClosed isClosed_singleton
  have hmem : ((x, C.tstar) : E d × ℝ) ∈ closure (P.D ∩ P.uhat ⁻¹' {0}) := by
    refine mem_closure_of_forall_sub P.μ_pos fun ε hε ↦ ?_
    have hsaus : ((x, C.tstar - ε) : E d × ℝ) ∈ sausage C :=
      mem_sausage_of_le C hx (by simp [hε.1]) (by simp; linarith [hε.2, P.μ_pos])
    exact ⟨mem_D_of_mem_sausage C hsaus, uhat_eq_zero_of_mem_sausage C hsaus⟩
  rw [hS.closure_eq] at hmem
  exact hmem.2

/-- If `ν¹ = e_t`, there is a rim witness `(x̄, t⋆) ∈ E` with
`|x̄ - x⋆| = λ₁`. -/
theorem exists_rim_mem (h : C.ν₁ = ((0 : E d), (1 : ℝ))) :
    ∃ xb : E d, ‖xb - C.xstar‖ = P.ℓ ∧ ((xb, C.tstar) : E d × ℝ) ∈ Eset := by
  have hq := C.q₁_mem_E₀
  rw [C.ν₁_eq_et_iff.1 h] at hq
  obtain ⟨-, k, hk, hkE⟩ := hq
  rw [mem_K₀_iff] at hk
  have heq : C.pstar + k = ((C.xstar + k.1, C.tstar) : E d × ℝ) := by
    ext
    · rfl
    · simp [hk.2, ContactData.tstar]
  rw [heq] at hkE
  refine ⟨C.xstar + k.1, ?_, hkE⟩
  rw [add_sub_cancel_left]
  refine le_antisymm hk.1 (not_lt.1 fun hlt ↦ not_mem_of_mem_topDisk C ?_ hkE)
  exact ⟨by rwa [mem_ball, dist_eq_norm, add_sub_cancel_left], rfl⟩

/-- Unwinding for the subsolution, bundled. If `ν¹ = e_t`: (a) `E ∩ 𝒮 = ∅` and `û = 0` on `𝒮`;
(b) `E ∩ 𝒟 = ∅` and `û = 0` on `𝒟̄`; (c) there is `x̄` with `|x̄ - x⋆| = λ₁` and `(x̄, t⋆) ∈ E`. -/
theorem unwind_u (h : C.ν₁ = ((0 : E d), (1 : ℝ))) :
    (∀ q ∈ sausage C, q ∉ Eset ∧ P.uhat q = 0) ∧
      (∀ q ∈ topDisk C, q ∉ Eset) ∧
      (∀ x : E d, ‖x - C.xstar‖ ≤ P.ℓ → P.uhat (x, C.tstar) = 0) ∧
      ∃ xb : E d, ‖xb - C.xstar‖ = P.ℓ ∧ ((xb, C.tstar) : E d × ℝ) ∈ Eset :=
  ⟨fun _ hq ↦ ⟨not_mem_of_mem_sausage C hq, uhat_eq_zero_of_mem_sausage C hq⟩,
    fun _ hq ↦ not_mem_of_mem_topDisk C hq, fun _ hx ↦ uhat_eq_zero_of_norm_le C hx,
    exists_rim_mem C h⟩

/-! ### Unwinding for the supersolution -/

/-- `v̂ > 0` on `𝒮`. -/
theorem vhat_pos_of_mem_sausage {q : E d × ℝ} (hq : q ∈ sausage C) : 0 < P.vhat q := by
  obtain ⟨e, he, hp⟩ := sausage_decomp C hq
  have h1 := C.dual_v₀_pos _ hp
  have h2 := infConv_le P.isCompact_K₀ P.continuousOn_vhat
    (fun k hk ↦ add_mem_D_of_mem_K₀ (mem_U₀_prod_of_mem_dualBallOpen C hp) hk)
    (mem_K₀_iff.2 ⟨he, rfl⟩ : ((e, 0) : E d × ℝ) ∈ P.K₀)
  rw [decomp_add] at h2
  exact h1.trans_le h2

/-- `v̂ > 0` on `𝒟` (by `Contact.bump_positivity_pos`). -/
theorem vhat_pos_of_mem_topDisk {q : E d × ℝ} (hq : q ∈ topDisk C) : 0 < P.vhat q := by
  obtain ⟨hq1, hq2⟩ := hq
  rw [mem_ball, dist_eq_norm] at hq1
  rw [mem_singleton_iff] at hq2
  have hμ := P.μ_pos
  set r := min (P.ℓ - ‖q.1 - C.xstar‖) √P.μ / 2 with hr
  have hr0 : 0 < r := by
    have := lt_min (sub_pos.2 hq1) (Real.sqrt_pos.2 hμ); rw [hr]; linarith
  have hr1 : r < P.ℓ - ‖q.1 - C.xstar‖ := by
    have := min_le_left (P.ℓ - ‖q.1 - C.xstar‖) √P.μ; rw [hr]; linarith
  have hr2 : r ^ 2 ≤ P.μ / 4 := by
    have h1 : r ≤ √P.μ / 2 := by
      have := min_le_right (P.ℓ - ‖q.1 - C.xstar‖) √P.μ; rw [hr]; linarith
    have h2 : r ^ 2 ≤ (√P.μ / 2) ^ 2 := pow_le_pow_left₀ hr0.le h1 2
    have h3 : (√P.μ / 2) ^ 2 = P.μ / 4 := by rw [div_pow, Real.sq_sqrt hμ.le]; norm_num
    linarith
  set δ := r ^ 2 / (4 * d + 4) with hδ
  have hd4 : (0 : ℝ) < 4 * d + 4 := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ r ^ 2 / 4 := div_le_div_of_nonneg_left (sq_nonneg r) (by norm_num)
    (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have htd : 4 * d * (C.tstar - (C.tstar - δ)) ≤ r ^ 2 := by
    rw [sub_sub_cancel, hδ, mul_div_assoc', div_le_iff₀ hd4]
    nlinarith [sq_nonneg r]
  have hnear : ∀ p ∈ closedBall q.1 r ×ˢ Icc (C.tstar - δ) C.tstar,
      ‖p.1 - C.xstar‖ < P.ℓ ∧ C.tstar - 2 * P.μ < p.2 := by
    rintro p ⟨hp1, hp2⟩
    rw [mem_closedBall, dist_eq_norm] at hp1
    have := norm_sub_le_norm_sub_add_norm_sub p.1 q.1 C.xstar
    exact ⟨by linarith, by linarith [hp2.1]⟩
  have hpos := bump_positivity_pos (O := U ×ˢ Ioc 0 T) (w := P.vhat)
    (P.continuousOn_vhat.mono fun p hp ↦ ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩)
    P.isSupercal_hat hr0 (by linarith : C.tstar - δ < C.tstar) htd
    (fun p hp ↦ mem_prod_of_near C ((hnear p hp).1.trans P.ℓ_lt_lam) (hnear p hp).2 hp.2.2)
    (fun p hp ↦ vhat_pos_of_mem_sausage C (mem_sausage_of_le C (hnear p
      ⟨hp.1, hp.2.1, hp.2.2.le⟩).1.le (by linarith [hp.2.2]) (by linarith [hp.2.1])))
  have : q = (q.1, C.tstar) := Prod.ext rfl hq2
  rwa [this]

/-- If `ν² = e_t`, there is a rim zero `(x̄, t⋆)`, `v̂(x̄, t⋆) = 0`,
with `|x̄ - x⋆| = λ₁`. -/
theorem exists_rim_zero (h : C.ν₂ = ((0 : E d), (1 : ℝ))) :
    ∃ xb : E d, ‖xb - C.xstar‖ = P.ℓ ∧ P.vhat (xb, C.tstar) = 0 := by
  have hv := C.v₀_q₂
  rw [C.ν₂_eq_et_iff.1 h] at hv
  obtain ⟨k, hk, hkeq⟩ := exists_infConv_eq P.isCompact_K₀ ⟨0, P.zero_mem_K₀⟩
    P.continuousOn_vhat fun k hk ↦ add_mem_D_of_mem_K₀ (pstar_mem_U₀_prod C) hk
  have hk0 : P.vhat (C.pstar + k) = 0 := by rw [← hkeq]; exact hv
  rw [mem_K₀_iff] at hk
  have heq : C.pstar + k = ((C.xstar + k.1, C.tstar) : E d × ℝ) := by
    ext
    · rfl
    · simp [hk.2, ContactData.tstar]
  rw [heq] at hk0
  refine ⟨C.xstar + k.1, ?_, hk0⟩
  rw [add_sub_cancel_left]
  refine le_antisymm hk.1 (not_lt.1 fun hlt ↦ (vhat_pos_of_mem_topDisk C ?_).ne' hk0)
  exact ⟨by rwa [mem_ball, dist_eq_norm, add_sub_cancel_left], rfl⟩

/-- Unwinding for the supersolution, bundled. If `ν² = e_t`: (a) `v̂ > 0` on `𝒮`;
(b) `v̂ > 0` on `𝒟`; (c) there is `x̄` with `|x̄ - x⋆| = λ₁` and `v̂(x̄, t⋆) = 0`. -/
theorem unwind_v (h : C.ν₂ = ((0 : E d), (1 : ℝ))) :
    (∀ q ∈ sausage C, 0 < P.vhat q) ∧ (∀ q ∈ topDisk C, 0 < P.vhat q) ∧
      ∃ xb : E d, ‖xb - C.xstar‖ = P.ℓ ∧ P.vhat (xb, C.tstar) = 0 :=
  ⟨fun _ hq ↦ vhat_pos_of_mem_sausage C hq, fun _ hq ↦ vhat_pos_of_mem_topDisk C hq,
    exists_rim_zero C h⟩

end Polar

end BernoulliComparison
