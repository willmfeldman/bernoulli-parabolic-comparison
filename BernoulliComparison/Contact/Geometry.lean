/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Crossing.Instance
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Euclidean space-time geometry at the contact point

Helpers for the contact analysis. `E d × ℝ` carries the sup metric, so Euclidean space-time balls
are written explicitly.

* `stNorm k = √(‖k.1‖² + k.2²)`, the Euclidean space-time norm, realised as the norm of
  `WithLp.toLp 2 k`, so that the triangle inequality is available (`stNorm_add_le`).
* `stBallOpen c r = {k | ‖k.1 - c.1‖² + (k.2 - c.2)² < r²}`, the open Euclidean space-time ball
  (`stBall` of `Convolution/Kernel.lean` is the closed one).
* `Config.dualCentre p = p - μ e_t = (p.1, p.2 - μ)`, the dual centre `p̂` of the dual-ball lemma;
  `Config.mem_add_B_iff`: `q ∈ p + B⁻_μ ↔ q ∈ B̄_μ(p̂)`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

variable {d : ℕ}

/-! ### The Euclidean space-time norm -/

/-- The Euclidean space-time norm `√(‖k.1‖² + k.2²)`. -/
noncomputable def stNorm (k : E d × ℝ) : ℝ := ‖WithLp.toLp 2 k‖

theorem stNorm_sq (k : E d × ℝ) : stNorm k ^ 2 = ‖k.1‖ ^ 2 + k.2 ^ 2 := by
  rw [stNorm, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rfl

theorem stNorm_nonneg (k : E d × ℝ) : 0 ≤ stNorm k := norm_nonneg _

theorem stNorm_add_le (k k' : E d × ℝ) : stNorm (k + k') ≤ stNorm k + stNorm k' := by
  unfold stNorm
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

theorem stNorm_neg (k : E d × ℝ) : stNorm (-k) = stNorm k := by
  unfold stNorm
  rw [WithLp.toLp_neg, norm_neg]

theorem stNorm_sub_comm (k k' : E d × ℝ) : stNorm (k - k') = stNorm (k' - k) := by
  rw [← neg_sub, stNorm_neg]

theorem stNorm_sub_le (a b c : E d × ℝ) : stNorm (a - c) ≤ stNorm (a - b) + stNorm (b - c) := by
  have := stNorm_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

theorem stNorm_smul (s : ℝ) (k : E d × ℝ) : stNorm (s • k) = |s| * stNorm k := by
  unfold stNorm
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem stNorm_le_iff {k : E d × ℝ} {r : ℝ} (hr : 0 ≤ r) :
    stNorm k ≤ r ↔ ‖k.1‖ ^ 2 + k.2 ^ 2 ≤ r ^ 2 := by
  rw [← stNorm_sq, sq_le_sq₀ (stNorm_nonneg k) hr]

theorem stNorm_lt_iff {k : E d × ℝ} {r : ℝ} (hr : 0 ≤ r) :
    stNorm k < r ↔ ‖k.1‖ ^ 2 + k.2 ^ 2 < r ^ 2 := by
  rw [← stNorm_sq, sq_lt_sq₀ (stNorm_nonneg k) hr]

/-- The Euclidean norm is at most the sum of the spatial and temporal norms. -/
theorem stNorm_le_add (k : E d × ℝ) : stNorm k ≤ ‖k.1‖ + |k.2| := by
  rw [stNorm_le_iff (by positivity)]
  have := norm_nonneg k.1
  have := abs_nonneg k.2
  nlinarith [sq_abs k.2]

/-- The Euclidean norm is at most twice the sup norm. -/
theorem stNorm_le_two_mul_norm (k : E d × ℝ) : stNorm k ≤ 2 * ‖k‖ := by
  refine (stNorm_le_add k).trans ?_
  have h1 : ‖k.1‖ ≤ ‖k‖ := norm_fst_le k
  have h2 : |k.2| ≤ ‖k‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le k
  linarith

theorem norm_fst_le_stNorm (k : E d × ℝ) : ‖k.1‖ ≤ stNorm k := by
  rw [← sq_le_sq₀ (norm_nonneg _) (stNorm_nonneg k), stNorm_sq]
  nlinarith [sq_nonneg k.2]

theorem abs_snd_le_stNorm (k : E d × ℝ) : |k.2| ≤ stNorm k := by
  rw [← sq_le_sq₀ (abs_nonneg _) (stNorm_nonneg k), stNorm_sq, sq_abs]
  nlinarith [sq_nonneg ‖k.1‖]

theorem continuous_stNorm : Continuous (stNorm : E d × ℝ → ℝ) :=
  continuous_norm.comp (WithLp.prodContinuousLinearEquiv 2 ℝ (E d) ℝ).symm.continuous

/-! ### Open Euclidean space-time balls -/

/-- The open Euclidean space-time ball `B_r(c)`. -/
def stBallOpen (c : E d × ℝ) (r : ℝ) : Set (E d × ℝ) :=
  {k | ‖k.1 - c.1‖ ^ 2 + (k.2 - c.2) ^ 2 < r ^ 2}

theorem mem_stBallOpen {c k : E d × ℝ} {r : ℝ} :
    k ∈ stBallOpen c r ↔ ‖k.1 - c.1‖ ^ 2 + (k.2 - c.2) ^ 2 < r ^ 2 :=
  Iff.rfl

theorem stBallOpen_subset_stBall (c : E d × ℝ) (r : ℝ) : stBallOpen c r ⊆ stBall c r :=
  fun _ hk ↦ mem_stBall.2 (le_of_lt hk)

theorem mem_stBall_iff_stNorm {c k : E d × ℝ} {r : ℝ} (hr : 0 ≤ r) :
    k ∈ stBall c r ↔ stNorm (k - c) ≤ r := by
  rw [stNorm_le_iff hr, mem_stBall]; rfl

theorem mem_stBallOpen_iff_stNorm {c k : E d × ℝ} {r : ℝ} (hr : 0 ≤ r) :
    k ∈ stBallOpen c r ↔ stNorm (k - c) < r := by
  rw [stNorm_lt_iff hr, mem_stBallOpen]; rfl

theorem isOpen_stBallOpen (c : E d × ℝ) (r : ℝ) : IsOpen (stBallOpen c r) :=
  isOpen_lt (by fun_prop) continuous_const

/-- Points of the closed ball on the segment towards the centre lie in the open ball. -/
theorem lineMap_mem_stBallOpen {c k : E d × ℝ} {r : ℝ} (hr : 0 < r) (hk : k ∈ stBall c r)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : c + s • (k - c) ∈ stBallOpen c r := by
  rw [mem_stBall_iff_stNorm hr.le] at hk
  rw [mem_stBallOpen_iff_stNorm hr.le, add_sub_cancel_left, stNorm_smul, abs_of_nonneg hs0]
  calc s * stNorm (k - c) ≤ s * r := mul_le_mul_of_nonneg_left hk hs0
    _ < 1 * r := mul_lt_mul_of_pos_right hs1 hr
    _ = r := one_mul r

namespace Crossing

namespace Config

variable {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} (P : Config U Q T u v Eset)

/-- The dual centre `p̂ = p - μ e_t` used in the dual-ball lemma (`Contact/Balls.lean`). -/
def dualCentre (p : E d × ℝ) : E d × ℝ := (p.1, p.2 - P.μ)

/-- `q ∈ p + B⁻_μ` iff `q ∈ B̄_μ(p̂)`. -/
theorem sub_mem_B_iff {p q : E d × ℝ} : q - p ∈ P.B ↔ q ∈ stBall (P.dualCentre p) P.μ := by
  rw [B, mem_backBall, mem_stBall, dualCentre]
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> convert h using 2 <;> ring

/-- `p + k ∈ B̄_μ(p̂)` for `k ∈ B⁻_μ`. -/
theorem add_mem_stBall_of_mem_B {p k : E d × ℝ} (hk : k ∈ P.B) :
    p + k ∈ stBall (P.dualCentre p) P.μ := by
  rw [← sub_mem_B_iff, add_sub_cancel_left]; exact hk

end Config

end Crossing

end BernoulliComparison
