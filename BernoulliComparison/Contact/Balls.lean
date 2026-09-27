/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.Structure

/-!
# The dual ball and the touching balls

The dual-ball lemma at a first contact point, and the location of the touching points.
Let `p⋆ = (x⋆, t⋆)` be a first contact point and `p̂ = p⋆ - μ e_t`
(`Config.dualCentre`). Then `B̄_μ(p̂) = p⋆ + B ⊆ B̄_μ(x⋆) × [t⋆ - 2μ, t⋆] ⊆ U₀ × (0, T]`
(`dualBall_subset_prod`, `prod_subset_U₀_Ioc`), and:

(a) `E₀ ∩ B_μ(p̂) = ∅` (`dual_not_mem_E₀`) and `u₀ = 0` on `B̄_μ(p̂)` (`dual_u₀_eq_zero`);
(b) `v₀ > 0` on `B_μ(p̂)` (`dual_v₀_pos`);
(c) there are `q₁ ∈ E₀`, `q₂` with `|qᵢ - p̂| = μ`, `u₀(q₁) = 0`, `v₀(q₂) = 0`
(`exists_q₁`, `exists_q₂`);
(d) with the centres `qᵢ + μ e_t`: `B̄_μ(q₁ + μ e_t) ∩ D₁ ⊆ E₁` (`interior_ball`) and
`B̄_μ(q₂ + μ e_t) ∩ D₁ ⊆ {v₁ = 0}` (`exterior_ball`);
(e) `E₁ ∩ B̄_μ(q₂ + μ e_t) ∩ {t < t⋆} = ∅` (`exterior_past`) and
`E₁ ∩ B_μ(q₂ + μ e_t) ∩ {t ≤ t⋆} = ∅` (`exterior_open`);
(f) `B̄_μ(q₁ + μ e_t) ∩ D₁ ∩ {t < t⋆} ⊆ {v₁ > 0}` (`interior_past`).

All balls are Euclidean space-time balls (`stBall`, `stBallOpen`), not balls of the sup
metric on `E d × ℝ`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Contact

open Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset} {p : E d × ℝ}

/-! ### Geometry of the dual ball -/

theorem dualCentre_sub (a b : E d × ℝ) : P.dualCentre a - P.dualCentre b = a - b := by
  ext <;> simp [dualCentre]

/-- `q - p' ∈ B` as soon as `|q - p̂| + |p' - p| ≤ μ` (Euclidean norms). -/
theorem sub_mem_B_of_stNorm_le {p' q : E d × ℝ}
    (hle : stNorm (q - P.dualCentre p) + stNorm (p' - p) ≤ P.μ) : q - p' ∈ P.B := by
  rw [sub_mem_B_iff, mem_stBall_iff_stNorm P.μ_pos.le]
  have h1 : q - P.dualCentre p' = (q - P.dualCentre p) + (p - p') := by
    rw [← dualCentre_sub (P := P) p p']; abel
  rw [h1]
  calc stNorm (q - P.dualCentre p + (p - p'))
      ≤ stNorm (q - P.dualCentre p) + stNorm (p - p') := stNorm_add_le _ _
    _ = stNorm (q - P.dualCentre p) + stNorm (p' - p) := by rw [stNorm_sub_comm p p']
    _ ≤ P.μ := hle

/-- Points of a closure are close in the Euclidean space-time norm. -/
theorem exists_stNorm_lt_of_mem_closure {s : Set (E d × ℝ)} (hp : p ∈ closure s) {η : ℝ}
    (hη : 0 < η) : ∃ p' ∈ s, stNorm (p' - p) < η := by
  obtain ⟨p', hp's, hdist⟩ := Metric.mem_closure_iff.mp hp (η / 2) (half_pos hη)
  refine ⟨p', hp's, (stNorm_le_two_mul_norm _).trans_lt ?_⟩
  rw [dist_comm, dist_eq_norm] at hdist
  linarith

/-- `B̄_μ(p̂) ⊆ B̄_μ(x⋆) × [t⋆ - 2μ, t⋆]`. -/
theorem dualBall_subset_prod (P : Config U Q T u v Eset) (p : E d × ℝ) :
    stBall (P.dualCentre p) P.μ ⊆ closedBall p.1 P.μ ×ˢ Icc (p.2 - 2 * P.μ) p.2 := by
  intro q hq
  rw [mem_stBall] at hq
  simp only [dualCentre] at hq
  have hμ := P.μ_pos
  have h1 : ‖q.1 - p.1‖ ^ 2 ≤ P.μ ^ 2 := by nlinarith [sq_nonneg (q.2 - (p.2 - P.μ))]
  have h2 : (q.2 - (p.2 - P.μ)) ^ 2 ≤ P.μ ^ 2 := by nlinarith [sq_nonneg ‖q.1 - p.1‖]
  have h1' := abs_le_of_sq_le_sq' h2 hμ.le
  refine ⟨?_, by linarith [h1'.1], by linarith [h1'.2]⟩
  rw [mem_closedBall, dist_eq_norm]
  exact (sq_le_sq₀ (norm_nonneg _) hμ.le).mp h1

/-- `B_μ(p̂) ⊆ B_μ(x⋆) × (t⋆ - 2μ, t⋆)`. -/
theorem dualBallOpen_subset_prod (P : Config U Q T u v Eset) (p : E d × ℝ) :
    stBallOpen (P.dualCentre p) P.μ ⊆ ball p.1 P.μ ×ˢ Ioo (p.2 - 2 * P.μ) p.2 := by
  intro q hq
  rw [mem_stBallOpen] at hq
  simp only [dualCentre] at hq
  have hμ := P.μ_pos
  have h1 : ‖q.1 - p.1‖ ^ 2 < P.μ ^ 2 := by nlinarith [sq_nonneg (q.2 - (p.2 - P.μ))]
  have h2 : (q.2 - (p.2 - P.μ)) ^ 2 < P.μ ^ 2 := by nlinarith [sq_nonneg ‖q.1 - p.1‖]
  have h1' := abs_lt_of_sq_lt_sq' h2 hμ.le
  refine ⟨?_, by linarith [h1'.1], by linarith [h1'.2]⟩
  rw [mem_ball, dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) hμ.le).mp h1

/-- Points of the sphere `|q - p̂| = μ` are in `B̄_μ(p̂)`. -/
theorem mem_stBall_of_sphere {q : E d × ℝ}
    (hq : ‖q.1 - p.1‖ ^ 2 + (q.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2) :
    q ∈ stBall (P.dualCentre p) P.μ := by
  rw [mem_stBall]; exact hq.le

/-- A continuous function vanishing on the open ball vanishes on the closed ball. -/
theorem eq_zero_on_stBall {c : E d × ℝ} {r : ℝ} (hr : 0 < r) {w : E d × ℝ → ℝ}
    (hw : ContinuousOn w (stBall c r)) (h0 : ∀ q ∈ stBallOpen c r, w q = 0) :
    ∀ q ∈ stBall c r, w q = 0 := by
  intro q hq
  set g : ℝ → E d × ℝ := fun s ↦ c + s • (q - c) with hg
  have hgc : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hmaps : MapsTo g (Icc 0 1) (stBall c r) := by
    intro s hs
    rw [mem_stBall_iff_stNorm hr.le] at hq ⊢
    rw [hg, add_sub_cancel_left, stNorm_smul, abs_of_nonneg hs.1]
    nlinarith [stNorm_nonneg (q - c), hs.2]
  have hfc : ContinuousOn (w ∘ g) (Icc 0 1) := hw.comp hgc.continuousOn hmaps
  have heq : EqOn (w ∘ g) (fun _ ↦ (0 : ℝ)) (Ico 0 1) := fun s hs ↦
    h0 _ (lineMap_mem_stBallOpen hr hq hs.1 hs.2)
  have := heq.of_subset_closure hfc continuousOn_const Ico_subset_Icc_self
    (by rw [closure_Ico zero_ne_one])
  simpa [hg] using this (right_mem_Icc.2 zero_le_one)

variable (h : P.IsFirstContact p)
include h

/-- `B̄_μ(x⋆) × [t⋆ - 2μ, t⋆] ⊆ U₀ × (0, T]`. -/
theorem prod_subset_U₀_Ioc :
    closedBall p.1 P.μ ×ˢ Icc (p.2 - 2 * P.μ) p.2 ⊆ P.U₀ ×ˢ Ioc 0 T := by
  rintro q ⟨hq1, hq2⟩
  rw [mem_closedBall, dist_eq_norm] at hq1
  refine ⟨?_, by linarith [h.two_μ_lt, hq2.1], hq2.2.trans h.le_T⟩
  simpa using P.add_mem_U₀_of_mem_U₁ h.fst_mem_U₁ hq1

/-- `B̄_μ(p̂) ⊆ U₀ × (0, T]`. -/
theorem dualBall_subset_U₀_Ioc : stBall (P.dualCentre p) P.μ ⊆ P.U₀ ×ˢ Ioc 0 T :=
  (dualBall_subset_prod P p).trans (prod_subset_U₀_Ioc h)

/-- `B̄_μ(p̂) ⊆ D₀`. -/
theorem dualBall_subset_D₀ : stBall (P.dualCentre p) P.μ ⊆ P.D₀ :=
  (dualBall_subset_U₀_Ioc h).trans P.prod_Ioc_subset_D₀

/-- `B_μ(p̂) ⊆ (U₁ × (2μ, T]) ∩ {t < t⋆}` (room); in particular `B_μ(p̂) ⊆ D₁ ∩ {t < t⋆}`. -/
theorem dualBallOpen_subset_past :
    stBallOpen (P.dualCentre p) P.μ ⊆ (P.U₁ ×ˢ Ioc (2 * P.μ) T) ∩ {q | q.2 < p.2} := by
  intro q hq
  obtain ⟨hq1, hq2⟩ := dualBallOpen_subset_prod P p hq
  rw [mem_ball, dist_eq_norm] at hq1
  have h2 := h.two_lam_lt_r₀
  have h3 := P.μ_lt_lam
  have h4 := P.r₀_pos
  exact ⟨h.mem_room (by linarith) (by linarith [hq2.1]) hq2.2.le, hq2.2⟩

/-! ### (a), (b) -/

/-- Dual-ball lemma (a): `E₀ ∩ B_μ(p̂) = ∅`. -/
theorem dual_not_mem_E₀ : ∀ q ∈ stBallOpen (P.dualCentre p) P.μ, q ∉ P.E₀ := by
  intro q hq hqE
  rw [mem_stBallOpen_iff_stNorm P.μ_pos.le] at hq
  obtain ⟨p', ⟨⟨hp'D, hp'E⟩, -⟩, hp'⟩ := exists_stNorm_lt_of_mem_closure
    (contact_structure_exterior_past h) (sub_pos.2 hq)
  have hB : q - p' ∈ P.B := sub_mem_B_of_stNorm_le (by linarith)
  refine hp'E ?_
  rw [E₁_eq]
  exact ⟨hp'D, q - p', hB, by rwa [add_sub_cancel]⟩

/-- Dual-ball lemma (a): `u₀ = 0` on `B̄_μ(p̂)`. -/
theorem dual_u₀_eq_zero : ∀ q ∈ stBall (P.dualCentre p) P.μ, P.u₀ q = 0 := by
  refine eq_zero_on_stBall P.μ_pos (P.continuousOn_u₀.mono (dualBall_subset_D₀ h)) ?_
  intro q hq
  have hqD := dualBall_subset_D₀ h (stBallOpen_subset_stBall _ _ hq)
  refine le_antisymm (not_lt.1 fun hpos ↦ dual_not_mem_E₀ h q hq ?_) (P.u₀_nonneg hqD)
  exact P.mem_E₀_of_u₀_pos hqD hpos

/-- Dual-ball lemma (b): `v₀ > 0` on `B_μ(p̂)`. -/
theorem dual_v₀_pos : ∀ q ∈ stBallOpen (P.dualCentre p) P.μ, 0 < P.v₀ q := by
  intro q hq
  rw [mem_stBallOpen_iff_stNorm P.μ_pos.le] at hq
  obtain ⟨p', ⟨hp'D, hp'v, -⟩, hp'⟩ := exists_stNorm_lt_of_mem_closure
    (contact_structure_pos_past h).2 (sub_pos.2 hq)
  have hB : q - p' ∈ P.B := sub_mem_B_of_stNorm_le (by linarith)
  have hle := infConv_le P.isCompact_B P.continuousOn_v₀
    (P.convStep_zero_one.closedDomain_add p' hp'D) hB
  rw [add_sub_cancel, ← P.v₁_eq hp'D] at hle
  exact hp'v.trans_le hle

/-! ### (c) the touching points `q₁`, `q₂` -/

/-- Dual-ball lemma (c), interior: there is `q₁ ∈ E₀` with `|q₁ - p̂| = μ` and
`u₀(q₁) = 0`. -/
theorem exists_q₁ : ∃ q₁ ∈ P.E₀,
    ‖q₁.1 - p.1‖ ^ 2 + (q₁.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2 ∧ P.u₀ q₁ = 0 := by
  have hpE := h.mem_E₁
  rw [E₁_eq] at hpE
  obtain ⟨-, k, hk, hkE⟩ := hpE
  have hball := P.add_mem_stBall_of_mem_B (p := p) hk
  refine ⟨p + k, hkE, ?_, dual_u₀_eq_zero h _ hball⟩
  rw [mem_stBall] at hball
  have hnot : ¬ (p + k) ∈ stBallOpen (P.dualCentre p) P.μ := fun hin ↦
    dual_not_mem_E₀ h _ hin hkE
  rw [mem_stBallOpen, not_lt] at hnot
  exact le_antisymm hball hnot

/-- Dual-ball lemma (c), exterior: there is `q₂` with `|q₂ - p̂| = μ` and `v₀(q₂) = 0`
(a minimizer of `v₀` on `p⋆ + B`). -/
theorem exists_q₂ : ∃ q₂ : E d × ℝ,
    ‖q₂.1 - p.1‖ ^ 2 + (q₂.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2 ∧ P.v₀ q₂ = 0 := by
  have hpD := h.mem_D₁
  obtain ⟨k, hk, hkeq⟩ := exists_infConv_eq P.isCompact_B ⟨0, P.zero_mem_B⟩ P.continuousOn_v₀
    (P.convStep_zero_one.closedDomain_add p hpD)
  have hv : P.v₀ (p + k) = 0 := by
    rw [← hkeq, ← P.v₁_eq hpD]; exact (zero_contact h).2
  have hball := P.add_mem_stBall_of_mem_B (p := p) hk
  refine ⟨p + k, ?_, hv⟩
  rw [mem_stBall] at hball
  have hnot : ¬ (p + k) ∈ stBallOpen (P.dualCentre p) P.μ := fun hin ↦
    (dual_v₀_pos h _ hin).ne' hv
  rw [mem_stBallOpen, not_lt] at hnot
  exact le_antisymm hball hnot

omit h

/-! ### (d)–(f) the interior and exterior balls -/

/-- Dual-ball lemma (d), interior ball: if `q₁ ∈ E₀` then
`B̄_μ(q₁ + μ e_t) ∩ D₁ ⊆ E₁`. -/
theorem interior_ball {q₁ : E d × ℝ} (hq₁ : q₁ ∈ P.E₀) :
    ∀ p' ∈ P.D₁, p' ∈ stBall (q₁ + (0, P.μ)) P.μ → p' ∈ P.E₁ := by
  intro p' hp'D hp'
  have hB : q₁ - p' ∈ P.B := by
    rw [sub_mem_B_iff, mem_stBall]
    rw [mem_stBall] at hp'
    simp only [dualCentre, Prod.fst_add, Prod.snd_add, add_zero] at hp' ⊢
    rw [norm_sub_rev]
    convert hp' using 2; ring
  rw [E₁_eq]
  exact ⟨hp'D, q₁ - p', hB, by rwa [add_sub_cancel]⟩

/-- Dual-ball lemma (d), exterior ball: if `v₀(q₂) = 0` then
`B̄_μ(q₂ + μ e_t) ∩ D₁ ⊆ {v₁ = 0}`. -/
theorem exterior_ball {q₂ : E d × ℝ} (hq₂ : P.v₀ q₂ = 0) :
    ∀ p' ∈ P.D₁, p' ∈ stBall (q₂ + (0, P.μ)) P.μ → P.v₁ p' = 0 := by
  intro p' hp'D hp'
  have hB : q₂ - p' ∈ P.B := by
    rw [sub_mem_B_iff, mem_stBall]
    rw [mem_stBall] at hp'
    simp only [dualCentre, Prod.fst_add, Prod.snd_add, add_zero] at hp' ⊢
    rw [norm_sub_rev]
    convert hp' using 2; ring
  have hle := infConv_le P.isCompact_B P.continuousOn_v₀
    (P.convStep_zero_one.closedDomain_add p' hp'D) hB
  rw [add_sub_cancel, hq₂, ← P.v₁_eq hp'D] at hle
  exact le_antisymm hle (P.v₁_nonneg hp'D)

include h

/-- Dual-ball lemma (e), first part: `E₁ ∩ B̄_μ(q₂ + μ e_t) ∩ {t < t⋆} = ∅`. -/
theorem exterior_past {q₂ : E d × ℝ} (hq₂ : P.v₀ q₂ = 0) :
    ∀ p' ∈ P.E₁, p' ∈ stBall (q₂ + (0, P.μ)) P.μ → ¬ p'.2 < p.2 := fun p' hp'E hp' hlt ↦
  (contact_structure_pos h p' hp'E hlt).ne' (exterior_ball hq₂ p' (P.E₁_subset_D₁ hp'E) hp')

/-- Dual-ball lemma (e), second part: `E₁ ∩ B_μ(q₂ + μ e_t) ∩ {t ≤ t⋆} = ∅`. -/
theorem exterior_open {q₂ : E d × ℝ}
    (hq₂s : ‖q₂.1 - p.1‖ ^ 2 + (q₂.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2) (hq₂ : P.v₀ q₂ = 0) :
    ∀ p' ∈ P.E₁, p' ∈ stBallOpen (q₂ + (0, P.μ)) P.μ → ¬ p'.2 ≤ p.2 := by
  intro p' hp'E hp' hle
  rcases hle.lt_or_eq with hlt | heq
  · exact exterior_past h hq₂ p' hp'E (stBallOpen_subset_stBall _ _ hp') hlt
  have hμ := P.μ_pos
  -- `p'` is in the room
  have hq₂1 : ‖q₂.1 - p.1‖ ≤ P.μ := (dualBall_subset_prod P p (mem_stBall_of_sphere hq₂s)).1
  have hp'1 : ‖p'.1 - q₂.1‖ < P.μ := by
    rw [mem_stBallOpen] at hp'
    simp only [Prod.fst_add, add_zero] at hp'
    have : ‖p'.1 - q₂.1‖ ^ 2 < P.μ ^ 2 := by
      nlinarith [sq_nonneg (p'.2 - (q₂ + (0, P.μ)).2)]
    exact (sq_lt_sq₀ (norm_nonneg _) hμ.le).mp this
  have hroom : p' ∈ P.U₁ ×ˢ Ioc (2 * P.μ) T := by
    have h1 : ‖p'.1 - p.1‖ ≤ ‖p'.1 - q₂.1‖ + ‖q₂.1 - p.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 := h.two_lam_lt_r₀
    have h3 := P.μ_lt_lam
    exact h.mem_room (by linarith) (by linarith [P.r₀_pos]) heq.le
  -- past points of `E₁` at `p'` inside the open ball
  rw [mem_stBallOpen_iff_stNorm hμ.le] at hp'
  set ε := P.μ - stNorm (p' - (q₂ + (0, P.μ))) with hε
  obtain ⟨q, hqE, hqt, hq⟩ := P.past_points_of_mem hp'E hroom (sub_pos.2 hp')
  have hqn : stNorm (q - p') < ε := (stNorm_lt_iff (sub_pos.2 hp').le).2 hq
  have hqball : q ∈ stBall (q₂ + (0, P.μ)) P.μ := by
    rw [mem_stBall_iff_stNorm hμ.le]
    have := stNorm_sub_le q p' (q₂ + (0, P.μ))
    linarith
  exact exterior_past h hq₂ q hqE hqball (heq ▸ hqt)

/-- Dual-ball lemma (f): `B̄_μ(q₁ + μ e_t) ∩ D₁ ∩ {t < t⋆} ⊆ {v₁ > 0}`. -/
theorem interior_past {q₁ : E d × ℝ} (hq₁ : q₁ ∈ P.E₀) :
    ∀ p' ∈ P.D₁, p' ∈ stBall (q₁ + (0, P.μ)) P.μ → p'.2 < p.2 → 0 < P.v₁ p' :=
  fun p' hp'D hp' hlt ↦ contact_structure_pos h p' (interior_ball hq₁ p' hp'D hp') hlt

omit h

/-! ### Location of the touching points -/

/-- A point of the sphere `|q - p̂| = μ` has `‖q.1 - x⋆‖ ≤ μ` and `t⋆ - 2μ ≤ q.2 ≤ t⋆`. -/
theorem sphere_mem_prod {q : E d × ℝ}
    (hq : ‖q.1 - p.1‖ ^ 2 + (q.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2) :
    q ∈ closedBall p.1 P.μ ×ˢ Icc (p.2 - 2 * P.μ) p.2 :=
  dualBall_subset_prod P p (mem_stBall_of_sphere hq)

/-- A point of the sphere `|q - p̂| = μ` has `|q - p⋆| ≤ 2μ` (Euclidean). -/
theorem stNorm_sub_le_of_sphere {q : E d × ℝ}
    (hq : ‖q.1 - p.1‖ ^ 2 + (q.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2) :
    stNorm (q - p) ≤ 2 * P.μ := by
  have h1 : stNorm (q - P.dualCentre p) ≤ P.μ :=
    (mem_stBall_iff_stNorm P.μ_pos.le).1 (mem_stBall_of_sphere hq)
  have h2 : stNorm (P.dualCentre p - p) = P.μ := by
    have : P.dualCentre p - p = ((0 : E d), -P.μ) := by ext <;> simp [dualCentre]
    rw [← sq_eq_sq₀ (stNorm_nonneg _) P.μ_pos.le, stNorm_sq, this]
    simp
  have := stNorm_sub_le q (P.dualCentre p) p
  linarith

include h in
/-- A point of the sphere `|q - p̂| = μ` lies in `O₀ = (W⋆ ∩ U₀) × (0, T]` (`W⋆ = B_{2λ}(x⋆)`). -/
theorem sphere_mem_O₀ {q : E d × ℝ}
    (hq : ‖q.1 - p.1‖ ^ 2 + (q.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2) : q ∈ P.O₀ p.1 := by
  have hq' := sphere_mem_prod hq
  have hU := prod_subset_U₀_Ioc h hq'
  refine ⟨⟨?_, hU.1⟩, hU.2⟩
  have h1 := hq'.1
  rw [mem_closedBall] at h1
  rw [Config.Wstar, mem_ball]
  have := P.μ_lt_lam
  have := P.lam_pos
  linarith

include h in
/-- A point of the sphere `|q - p̂| = μ` lies in `O = (W⋆ ∩ U) × (0, T]`. -/
theorem sphere_mem_O {q : E d × ℝ}
    (hq : ‖q.1 - p.1‖ ^ 2 + (q.2 - (p.2 - P.μ)) ^ 2 = P.μ ^ 2) : q ∈ P.O p.1 := by
  have hq' := sphere_mem_O₀ h hq
  exact ⟨⟨hq'.1.1, P.U₀_subset hq'.1.2⟩, hq'.2⟩

end Contact

end BernoulliComparison
