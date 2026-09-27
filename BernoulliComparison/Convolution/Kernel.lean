/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Setting
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Convolution kernels with the Euclidean space-time norm

`E d × ℝ` carries the *sup* metric, so the Euclidean space-time balls used as convolution kernels
are defined explicitly:

* `stBall c r = {k | ‖k.1 - c.1‖² + (k.2 - c.2)² ≤ r²}`, the closed Euclidean space-time ball;
* `spDisk c r = {k | ‖k.1 - c.1‖ ≤ r ∧ k.2 = c.2}`, the closed spatial disk `D̄_r`;
* `backBall μ = stBall (0, -μ) μ`, the backward-shifted ball `B⁻_μ`, lying in
  `{-2μ ≤ k.2 ≤ 0}` and containing `0` on its boundary (so convolution only looks into the past);
* `diskBallKernel ℓ μ = spDisk 0 ℓ + backBall μ`, the kernel `K = D̄_{ℓ} ⊕ B⁻_μ` used in the
  crossing configuration (`Crossing/Config.lean`).

The lemmas are stated for general nonnegative radii (no special case `ℓ = 0`). In Lean the
spatial radius `λ₁` is written `ℓ` (`λ` is a keyword).
-/

@[expose] public section

open Set Metric Pointwise

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Euclidean space-time balls and spatial disks -/

/-- The closed Euclidean space-time ball `B̄_r(c)`. -/
def stBall (c : E d × ℝ) (r : ℝ) : Set (E d × ℝ) :=
  {k | ‖k.1 - c.1‖ ^ 2 + (k.2 - c.2) ^ 2 ≤ r ^ 2}

/-- The closed spatial disk `D̄_r(c) = B̄_r(c.1) × {c.2}`. -/
def spDisk (c : E d × ℝ) (r : ℝ) : Set (E d × ℝ) :=
  {k | ‖k.1 - c.1‖ ≤ r ∧ k.2 = c.2}

/-- The backward-shifted closed ball `B⁻_μ = B̄_μ(-μ e_t)`. -/
def backBall (μ : ℝ) : Set (E d × ℝ) :=
  stBall (0, -μ) μ

/-- The convolution kernel `K = D̄_{ℓ} ⊕ B⁻_μ`. -/
def diskBallKernel (ℓ μ : ℝ) : Set (E d × ℝ) :=
  spDisk 0 ℓ + backBall μ

theorem mem_stBall {c k : E d × ℝ} {r : ℝ} :
    k ∈ stBall c r ↔ ‖k.1 - c.1‖ ^ 2 + (k.2 - c.2) ^ 2 ≤ r ^ 2 :=
  Iff.rfl

theorem mem_spDisk {c k : E d × ℝ} {r : ℝ} :
    k ∈ spDisk c r ↔ ‖k.1 - c.1‖ ≤ r ∧ k.2 = c.2 :=
  Iff.rfl

theorem mem_backBall {k : E d × ℝ} {μ : ℝ} :
    k ∈ backBall μ ↔ ‖k.1‖ ^ 2 + (k.2 + μ) ^ 2 ≤ μ ^ 2 := by
  simp [backBall, mem_stBall, sub_neg_eq_add]

theorem isClosed_stBall (c : E d × ℝ) (r : ℝ) : IsClosed (stBall c r) :=
  isClosed_le (by fun_prop) continuous_const

theorem isClosed_spDisk (c : E d × ℝ) (r : ℝ) : IsClosed (spDisk c r) :=
  (isClosed_le (continuous_fst.sub continuous_const).norm continuous_const).inter
    (isClosed_eq continuous_snd continuous_const)

/-- A Euclidean space-time ball lies in the sup-metric ball of the same radius. -/
theorem stBall_subset_closedBall (c : E d × ℝ) (r : ℝ) : stBall c r ⊆ closedBall c |r| := by
  intro k hk
  rw [mem_stBall] at hk
  rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_eq_norm, Real.dist_eq]
  constructor
  · have h : ‖k.1 - c.1‖ ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg (k.2 - c.2)]
    have := sq_le_sq.mp h
    rwa [abs_norm] at this
  · have h : (k.2 - c.2) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg ‖k.1 - c.1‖]
    exact sq_le_sq.mp h

theorem isCompact_stBall (c : E d × ℝ) (r : ℝ) : IsCompact (stBall c r) :=
  (isCompact_closedBall c |r|).of_isClosed_subset (isClosed_stBall c r)
    (stBall_subset_closedBall c r)

theorem spDisk_subset_closedBall (c : E d × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    spDisk c r ⊆ closedBall c r := by
  rintro k ⟨hk1, hk2⟩
  rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_eq_norm, Real.dist_eq, hk2, sub_self,
    abs_zero]
  exact ⟨hk1, hr⟩

theorem isCompact_spDisk (c : E d × ℝ) (r : ℝ) : IsCompact (spDisk c r) := by
  rcases le_or_gt 0 r with hr | hr
  · exact (isCompact_closedBall c r).of_isClosed_subset (isClosed_spDisk c r)
      (spDisk_subset_closedBall c hr)
  · convert isCompact_empty
    ext k
    simp only [mem_spDisk, mem_empty_iff_false, iff_false, not_and]
    intro h
    exact absurd ((norm_nonneg _).trans h) (not_le.mpr hr)

theorem center_mem_stBall (c : E d × ℝ) (r : ℝ) : c ∈ stBall c r := by
  simp [mem_stBall, sq_nonneg]

theorem center_mem_spDisk (c : E d × ℝ) {r : ℝ} (hr : 0 ≤ r) : c ∈ spDisk c r := by
  simp [mem_spDisk, hr]

/-! ### The backward-shifted ball `B⁻_μ` -/

theorem isCompact_backBall (μ : ℝ) : IsCompact (backBall μ : Set (E d × ℝ)) :=
  isCompact_stBall _ _

theorem zero_mem_backBall (μ : ℝ) : (0 : E d × ℝ) ∈ backBall μ := by
  simp [mem_backBall]

theorem backBall_nonempty (μ : ℝ) : (backBall μ : Set (E d × ℝ)).Nonempty :=
  ⟨0, zero_mem_backBall μ⟩

/-- Points of `B⁻_μ` have spatial norm at most `μ`. -/
theorem norm_fst_le_of_mem_backBall {μ : ℝ} (hμ : 0 ≤ μ) {k : E d × ℝ} (hk : k ∈ backBall μ) :
    ‖k.1‖ ≤ μ := by
  rw [mem_backBall] at hk
  have h : ‖k.1‖ ^ 2 ≤ μ ^ 2 := by nlinarith [sq_nonneg (k.2 + μ)]
  exact (sq_le_sq₀ (norm_nonneg _) hμ).mp h

/-- Points of `B⁻_μ` have time coordinate in `[-2μ, 0]`. -/
theorem snd_mem_Icc_of_mem_backBall {μ : ℝ} (hμ : 0 ≤ μ) {k : E d × ℝ}
    (hk : k ∈ backBall μ) : k.2 ∈ Icc (-2 * μ) 0 := by
  rw [mem_backBall] at hk
  have h : (k.2 + μ) ^ 2 ≤ μ ^ 2 := by nlinarith [sq_nonneg ‖k.1‖]
  have h' := abs_le.mp ((sq_le_sq.mp h).trans_eq (abs_of_nonneg hμ))
  exact ⟨by linarith [h'.1], by linarith [h'.2]⟩

/-! ### The spatial disk `D̄_λ` centred at the origin -/

theorem norm_fst_le_of_mem_spDisk_zero {r : ℝ} {k : E d × ℝ} (hk : k ∈ spDisk 0 r) :
    ‖k.1‖ ≤ r := by
  simpa using hk.1

theorem snd_eq_zero_of_mem_spDisk_zero {r : ℝ} {k : E d × ℝ} (hk : k ∈ spDisk 0 r) :
    k.2 = 0 := by
  simpa using hk.2

theorem zero_mem_spDisk_zero {r : ℝ} (hr : 0 ≤ r) : (0 : E d × ℝ) ∈ spDisk 0 r :=
  center_mem_spDisk 0 hr

/-! ### The kernel `K = D̄_{ℓ} ⊕ B⁻_μ` -/

theorem isCompact_diskBallKernel (ℓ μ : ℝ) : IsCompact (diskBallKernel ℓ μ : Set (E d × ℝ)) :=
  (isCompact_spDisk 0 ℓ).add (isCompact_backBall μ)

theorem zero_mem_diskBallKernel {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (μ : ℝ) :
    (0 : E d × ℝ) ∈ diskBallKernel ℓ μ :=
  ⟨0, zero_mem_spDisk_zero hℓ, 0, zero_mem_backBall μ, add_zero 0⟩

theorem diskBallKernel_nonempty {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (μ : ℝ) :
    (diskBallKernel ℓ μ : Set (E d × ℝ)).Nonempty :=
  ⟨0, zero_mem_diskBallKernel hℓ μ⟩

/-- Points of `D̄_{ℓ} ⊕ B⁻_μ` have spatial norm at most `ℓ + μ` (the spatial radius). -/
theorem norm_fst_le_of_mem_diskBallKernel {ℓ μ : ℝ} (hμ : 0 ≤ μ) {k : E d × ℝ}
    (hk : k ∈ diskBallKernel ℓ μ) : ‖k.1‖ ≤ ℓ + μ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hk
  calc ‖(a + b).1‖ = ‖a.1 + b.1‖ := rfl
    _ ≤ ‖a.1‖ + ‖b.1‖ := norm_add_le _ _
    _ ≤ ℓ + μ := add_le_add (norm_fst_le_of_mem_spDisk_zero ha)
        (norm_fst_le_of_mem_backBall hμ hb)

/-- Points of `D̄_{ℓ} ⊕ B⁻_μ` have time coordinate in `[-2μ, 0]`. -/
theorem snd_mem_Icc_of_mem_diskBallKernel {ℓ μ : ℝ} (hμ : 0 ≤ μ) {k : E d × ℝ}
    (hk : k ∈ diskBallKernel ℓ μ) : k.2 ∈ Icc (-2 * μ) 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hk
  have h1 := snd_eq_zero_of_mem_spDisk_zero ha
  have h2 := snd_mem_Icc_of_mem_backBall hμ hb
  change a.2 + b.2 ∈ Icc (-2 * μ) 0
  rw [h1, zero_add]
  exact h2

/-- Two points of `D̄_{ℓ} ⊕ B⁻_μ` are at Euclidean space-time distance at most `2√2 λ`, with
`λ = ℓ + μ`: `|k - k'|² ≤ 8 λ²`. -/
theorem sq_dist_le_of_mem_diskBallKernel {ℓ μ : ℝ} (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ)
    {k k' : E d × ℝ} (hk : k ∈ diskBallKernel ℓ μ) (hk' : k' ∈ diskBallKernel ℓ μ) :
    ‖k.1 - k'.1‖ ^ 2 + (k.2 - k'.2) ^ 2 ≤ 8 * (ℓ + μ) ^ 2 := by
  have hx : ‖k.1 - k'.1‖ ≤ 2 * (ℓ + μ) :=
    (norm_sub_le _ _).trans (by linarith [norm_fst_le_of_mem_diskBallKernel hμ hk,
      norm_fst_le_of_mem_diskBallKernel hμ hk'])
  have ht := snd_mem_Icc_of_mem_diskBallKernel hμ hk
  have ht' := snd_mem_Icc_of_mem_diskBallKernel hμ hk'
  have ht2 : |k.2 - k'.2| ≤ 2 * (ℓ + μ) :=
    abs_le.mpr ⟨by linarith [ht.1, ht'.2], by linarith [ht.2, ht'.1]⟩
  have h1 : ‖k.1 - k'.1‖ ^ 2 ≤ (2 * (ℓ + μ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hx 2
  have h2 : (k.2 - k'.2) ^ 2 ≤ (2 * (ℓ + μ)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht2 2
  nlinarith

end BernoulliComparison
