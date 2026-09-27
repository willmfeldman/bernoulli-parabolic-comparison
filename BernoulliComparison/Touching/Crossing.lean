/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Parabolic

/-!
# Crossing (touching) on backward parabolic cylinders

`φ` crosses `u` from above in `S` at `p` if `p ∈ S` and, for all small `r > 0`,
`0 = max_{S ∩ Q_r(p)} (u - φ) = u(p) - φ(p)`, where `Q_r(x, t) = B_r(x) × (t - r², t]` is the
*backward* parabolic cylinder. We state this with one explicit radius (equivalent, since the
cylinders are monotone in `r`).

Touching is a derived notion in this project: the solution classes are the barrier ones
of `Interface/Parabolic.lean`; `Touching/Bridge.lean` proves that they satisfy the touching
alternatives.

Space-time is `E d × ℝ`; the spatial ball is the Euclidean ball `Metric.ball` on `E d`.

## Main definitions

* `parCyl x t r`: the backward cylinder `B_r(x) × (t - r², t]`.
* `CrossesFromAbove S u φ p`, `CrossesFromBelow S u φ p`.
* `IsCaloricSub O u`, `IsCaloricSuper O u`: viscosity sub/supersolutions of the heat equation in
  touching form, crossing in `O`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Backward parabolic cylinders -/

/-- The backward parabolic cylinder `Q_r(x, t) = B_r(x) × (t - r², t]` (Euclidean ball in `E d`). -/
def parCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := ball x r ×ˢ Ioc (t - r ^ 2) t

theorem mem_parCyl {x : E d} {t r : ℝ} {q : E d × ℝ} :
    q ∈ parCyl x t r ↔ dist q.1 x < r ∧ t - r ^ 2 < q.2 ∧ q.2 ≤ t := by
  simp [parCyl, mem_prod, mem_ball]

theorem self_mem_parCyl {x : E d} {t r : ℝ} (hr : 0 < r) : (x, t) ∈ parCyl x t r :=
  mem_parCyl.2 ⟨by simpa using hr, by nlinarith, le_rfl⟩

theorem parCyl_mono {x : E d} {t r r' : ℝ} (hr : 0 ≤ r) (hrr' : r ≤ r') :
    parCyl x t r ⊆ parCyl x t r' := by
  intro q hq
  rw [mem_parCyl] at hq ⊢
  refine ⟨hq.1.trans_le hrr', ?_, hq.2.2⟩
  nlinarith [hq.2.1]

/-! ### Crossing -/

/-- `φ` crosses `u` from above in `S` at `p`: `p ∈ S`, `u p = φ p`, and
`u ≤ φ` on `S ∩ Q_r(p)` for some `r > 0`. -/
def CrossesFromAbove (S : Set (E d × ℝ)) (u φ : E d × ℝ → ℝ) (p : E d × ℝ) : Prop :=
  p ∈ S ∧ u p = φ p ∧ ∃ r > 0, ∀ q ∈ S ∩ parCyl p.1 p.2 r, u q ≤ φ q

/-- `φ` crosses `u` from below in `S` at `p`: `p ∈ S`, `u p = φ p`, and
`φ ≤ u` on `S ∩ Q_r(p)` for some `r > 0`. -/
def CrossesFromBelow (S : Set (E d × ℝ)) (u φ : E d × ℝ → ℝ) (p : E d × ℝ) : Prop :=
  p ∈ S ∧ u p = φ p ∧ ∃ r > 0, ∀ q ∈ S ∩ parCyl p.1 p.2 r, φ q ≤ u q

section Crossing

variable {S T : Set (E d × ℝ)} {u v φ ψ : E d × ℝ → ℝ} {p : E d × ℝ}

namespace CrossesFromAbove

theorem mem (h : CrossesFromAbove S u φ p) : p ∈ S := h.1

theorem eq (h : CrossesFromAbove S u φ p) : u p = φ p := h.2.1

/-- The crossing inequality holds on every smaller cylinder. -/
theorem forall_le (h : CrossesFromAbove S u φ p) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ q ∈ S ∩ parCyl p.1 p.2 r, u q ≤ φ q := by
  obtain ⟨-, -, r₀, hr₀, hle⟩ := h
  exact ⟨r₀, hr₀, fun r hr hrr₀ q hq ↦ hle q ⟨hq.1, parCyl_mono hr.le hrr₀ hq.2⟩⟩

/-- Restriction to a smaller set containing the point. -/
theorem restrict_set (hST : S ⊆ T) (hpS : p ∈ S) (h : CrossesFromAbove T u φ p) :
    CrossesFromAbove S u φ p := by
  obtain ⟨-, heq, r, hr, hle⟩ := h
  exact ⟨hpS, heq, r, hr, fun q hq ↦ hle q ⟨hST hq.1, hq.2⟩⟩

/-- Crossing only depends on the set near `p` (backward in time): if `T ∩ Q_ρ(p) ⊆ S`, a crossing
in `S` is a crossing in `T`. -/
theorem of_local (h : CrossesFromAbove S u φ p) (hpT : p ∈ T) {ρ : ℝ} (hρ : 0 < ρ)
    (hTS : T ∩ parCyl p.1 p.2 ρ ⊆ S) : CrossesFromAbove T u φ p := by
  obtain ⟨-, heq, r, hr, hle⟩ := h
  refine ⟨hpT, heq, min r ρ, lt_min hr hρ, fun q hq ↦ hle q ⟨?_, ?_⟩⟩
  · exact hTS ⟨hq.1, parCyl_mono (le_min hr.le hρ.le) (min_le_right _ _) hq.2⟩
  · exact parCyl_mono (le_min hr.le hρ.le) (min_le_left _ _) hq.2

/-- A crossing on an open subset `O ⊆ T` is a crossing on `T`. -/
theorem extend_of_isOpen (h : CrossesFromAbove S u φ p) (hS : IsOpen S) (hST : S ⊆ T) :
    CrossesFromAbove T u φ p := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS p h.mem
  refine h.of_local (hST h.mem) (ρ := min ε 1) (lt_min hε one_pos) fun q hq ↦ hball ?_
  obtain ⟨hx, ht1, ht2⟩ := mem_parCyl.1 hq.2
  have hm : min ε 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 < min ε 1 := lt_min hε one_pos
  rw [mem_ball, Prod.dist_eq]
  refine max_lt (hx.trans_le (min_le_left _ _)) ?_
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [min_le_left ε 1]

/-- Shifting both functions by the same constant. -/
theorem sub_const (h : CrossesFromAbove S u φ p) (c : ℝ) :
    CrossesFromAbove S (fun q ↦ u q - c) (fun q ↦ φ q - c) p := by
  obtain ⟨hp, heq, r, hr, hle⟩ := h
  exact ⟨hp, by simp [heq], r, hr, fun q hq ↦ by linarith [hle q hq]⟩

/-- A local maximum of `u - φ` on `S` (backward cylinder) gives a crossing after shifting `φ` by
the contact value. -/
theorem of_local_max_add_const (hpS : p ∈ S) {r : ℝ} (hr : 0 < r)
    (hmax : ∀ q ∈ S ∩ parCyl p.1 p.2 r, u q - φ q ≤ u p - φ p) :
    CrossesFromAbove S u (fun q ↦ φ q + (u p - φ p)) p :=
  ⟨hpS, by ring, r, hr, fun q hq ↦ by linarith [hmax q hq]⟩

/-- Replacing the test function by one that agrees with it on `S` near `p`. -/
theorem congr (h : CrossesFromAbove S u φ p) {ρ : ℝ} (hρ : 0 < ρ)
    (hφψ : ∀ q ∈ S ∩ parCyl p.1 p.2 ρ, φ q = ψ q) : CrossesFromAbove S u ψ p := by
  obtain ⟨hp, heq, r, hr, hle⟩ := h
  have hr' : 0 ≤ min r ρ := le_min hr.le hρ.le
  refine ⟨hp, ?_, min r ρ, lt_min hr hρ, fun q hq ↦ ?_⟩
  · rw [heq, hφψ p ⟨hp, self_mem_parCyl hρ⟩]
  · rw [← hφψ q ⟨hq.1, parCyl_mono hr' (min_le_right _ _) hq.2⟩]
    exact hle q ⟨hq.1, parCyl_mono hr' (min_le_left _ _) hq.2⟩

end CrossesFromAbove

namespace CrossesFromBelow

theorem mem (h : CrossesFromBelow S u φ p) : p ∈ S := h.1

theorem eq (h : CrossesFromBelow S u φ p) : u p = φ p := h.2.1

/-- Crossing from below is crossing from above for the negatives. -/
theorem neg_iff : CrossesFromBelow S u φ p ↔ CrossesFromAbove S (-u) (-φ) p := by
  simp only [CrossesFromBelow, CrossesFromAbove, Pi.neg_apply, neg_inj, neg_le_neg_iff]

/-- The crossing inequality holds on every smaller cylinder. -/
theorem forall_le (h : CrossesFromBelow S u φ p) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ q ∈ S ∩ parCyl p.1 p.2 r, φ q ≤ u q := by
  obtain ⟨-, -, r₀, hr₀, hle⟩ := h
  exact ⟨r₀, hr₀, fun r hr hrr₀ q hq ↦ hle q ⟨hq.1, parCyl_mono hr.le hrr₀ hq.2⟩⟩

theorem restrict_set (hST : S ⊆ T) (hpS : p ∈ S) (h : CrossesFromBelow T u φ p) :
    CrossesFromBelow S u φ p :=
  neg_iff.2 ((neg_iff.1 h).restrict_set hST hpS)

theorem of_local (h : CrossesFromBelow S u φ p) (hpT : p ∈ T) {ρ : ℝ} (hρ : 0 < ρ)
    (hTS : T ∩ parCyl p.1 p.2 ρ ⊆ S) : CrossesFromBelow T u φ p :=
  neg_iff.2 ((neg_iff.1 h).of_local hpT hρ hTS)

theorem extend_of_isOpen (h : CrossesFromBelow S u φ p) (hS : IsOpen S) (hST : S ⊆ T) :
    CrossesFromBelow T u φ p :=
  neg_iff.2 ((neg_iff.1 h).extend_of_isOpen hS hST)

theorem sub_const (h : CrossesFromBelow S u φ p) (c : ℝ) :
    CrossesFromBelow S (fun q ↦ u q - c) (fun q ↦ φ q - c) p := by
  obtain ⟨hp, heq, r, hr, hle⟩ := h
  exact ⟨hp, by simp [heq], r, hr, fun q hq ↦ by linarith [hle q hq]⟩

theorem of_local_min_add_const (hpS : p ∈ S) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ q ∈ S ∩ parCyl p.1 p.2 r, u p - φ p ≤ u q - φ q) :
    CrossesFromBelow S u (fun q ↦ φ q + (u p - φ p)) p :=
  ⟨hpS, by ring, r, hr, fun q hq ↦ by linarith [hmin q hq]⟩

theorem congr (h : CrossesFromBelow S u φ p) {ρ : ℝ} (hρ : 0 < ρ)
    (hφψ : ∀ q ∈ S ∩ parCyl p.1 p.2 ρ, φ q = ψ q) : CrossesFromBelow S u ψ p :=
  neg_iff.2 ((neg_iff.1 h).congr hρ fun q hq ↦ by simp [hφψ q hq])

end CrossesFromBelow

end Crossing

/-! ### Viscosity sub/supersolutions of the heat equation (touching form) -/

/-- `u` is a viscosity subsolution of the heat equation in `O` (touching form):
whenever a `C^∞` function `φ` crosses `u` from above in `O` at `p`,
`(∂ₜφ - Δφ)(p) ≤ 0`. -/
def IsCaloricSub (O : Set (E d × ℝ)) (u : E d × ℝ → ℝ) : Prop :=
  ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ p, CrossesFromAbove O u φ p → dₜ φ p - lapₓ φ p ≤ 0

/-- `u` is a viscosity supersolution of the heat equation in `O` (touching form):
whenever a `C^∞` function `φ` crosses `u` from below in `O` at `p`,
`(∂ₜφ - Δφ)(p) ≥ 0`. -/
def IsCaloricSuper (O : Set (E d × ℝ)) (u : E d × ℝ → ℝ) : Prop :=
  ∀ φ : E d × ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ p, CrossesFromBelow O u φ p → 0 ≤ dₜ φ p - lapₓ φ p

/-- A subcaloric function on `O` is subcaloric on any `O' ⊆ O` which agrees with `O` near each of
its points (backward in time), e.g. any open `O' ⊆ O`. -/
theorem IsCaloricSub.mono {O O' : Set (E d × ℝ)} {u : E d × ℝ → ℝ} (h : IsCaloricSub O u)
    (hO'O : O' ⊆ O) (hO' : ∀ p ∈ O', ∃ ρ > 0, O ∩ parCyl p.1 p.2 ρ ⊆ O') : IsCaloricSub O' u := by
  intro φ hφ p hp
  obtain ⟨ρ, hρ, hsub⟩ := hO' p hp.mem
  exact h φ hφ p (hp.of_local (hO'O hp.mem) hρ hsub)

/-- A supercaloric function on `O` is supercaloric on any `O' ⊆ O` which agrees with `O` near each
of its points (backward in time). -/
theorem IsCaloricSuper.mono {O O' : Set (E d × ℝ)} {u : E d × ℝ → ℝ} (h : IsCaloricSuper O u)
    (hO'O : O' ⊆ O) (hO' : ∀ p ∈ O', ∃ ρ > 0, O ∩ parCyl p.1 p.2 ρ ⊆ O') :
    IsCaloricSuper O' u := by
  intro φ hφ p hp
  obtain ⟨ρ, hρ, hsub⟩ := hO' p hp.mem
  exact h φ hφ p (hp.of_local (hO'O hp.mem) hρ hsub)

end BernoulliComparison
