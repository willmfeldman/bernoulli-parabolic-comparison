/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Polar.Unwind
public import BernoulliComparison.Barriers.Slope
public import BernoulliComparison.Barriers.PolarRadial
public import BernoulliComparison.Heat.Domain

/-!
# The interior north pole (N1)

At a contact point, the interior normal is not the north pole: `ν¹ ≠ e_t`
(`no_north_interior`).

Proof. Suppose `ν¹ = e_t` and let `w₁ = (x̄, t⋆) ∈ E`, `|x̄ - x⋆| = λ₁`, be the rim
witness given by `exists_rim_mem`. In rim coordinates `y = |x - x⋆| - λ₁`, `s = t⋆ - t`:

1. (domain) `Ω₁ = {0 < s < τ, A√s < y < h}` (`rimOuter`) is open, bounded, lies below `t⋆`, in
   `U × (0, T]` and in the domain `G₊` of the outer barrier `b₊` (`Barriers.polar_barrier_outer`);
2. (comparison, `outer_comparison`) `κ û ≤ b₊` on `Ω̄₁` for some `κ > 0`, by
   `Heat.domain_comparison_sub`: on the lateral side `y = A√s` and on the part of the bottom inside
   the sausage `û = 0` (`uhat_eq_zero_of_mem_sausage`), elsewhere on `∂Ω₁ ∩ {t < t⋆}` the
   barrier is at least `min(h/2, z_τ)^{1+ϑ}`;
3. (slope bound near `w₁`) on `N = B̄_ς(x̄) × [t⋆ - τ', t⋆]`: `E ∩ N ⊆ {|x - x⋆| ≥ λ₁}` and
   `û ≤ (c₁/2) (|x - x⋆| - λ₁)₊` on `E ∩ N`, from `b₊ ≤ y (y + √s)^ϑ`;
4. `Barriers.slope_sub_static` gives `w₁ ∉ E`, a contradiction.

The comparison is written as `κ û ≤ b₊`, which is `û ≤ K b₊` with `K = 1/κ`; the constant is
`κ = min(h/2, z_τ)^{1+ϑ} / (M + 1)` with `M ≥ max_D û`. The hypothesis `d ≥ 1` is not needed:
the rim witness forces it.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Polar

open Crossing Config Contact Barriers

variable {d : ℕ}

/-- A vector of positive norm exists only if `d ≥ 1`. -/
theorem one_le_d_of_norm_eq {x y : E d} {r : ℝ} (hr : 0 < r) (h : ‖x - y‖ = r) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    have : x - y = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at h
    exact hr.ne h
  · exact hd

variable {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset} (C : ContactData P)

/-! ### Rim coordinates as continuous functions -/

theorem continuous_rimS : Continuous fun q : E d × ℝ ↦ C.tstar - q.2 := by fun_prop

theorem continuous_rimY : Continuous fun q : E d × ℝ ↦ ‖q.1 - C.xstar‖ - P.ℓ := by fun_prop

theorem continuous_rimWall : Continuous fun q : E d × ℝ ↦ aperture P * √(C.tstar - q.2) :=
  continuous_const.mul (continuous_rimS C).sqrt

/-- Points of the closed rim region `{0 ≤ s ≤ τ, y ≤ h}` have `ρ < λ` and `0 ≤ s < 2μ`. -/
theorem rim_near {q : E d × ℝ} (hs0 : 0 ≤ C.tstar - q.2) (hsτ : C.tstar - q.2 ≤ rimTime P)
    (hy : ‖q.1 - C.xstar‖ - P.ℓ ≤ rimWidth P) :
    ‖q.1 - C.xstar‖ < P.lam ∧ C.tstar - 2 * P.μ < q.2 ∧ q.2 ≤ C.tstar := by
  have h1 := rimWidth_le_μ P
  have h2 := rimTime_le_μ P
  have hμ := P.μ_pos
  refine ⟨?_, by linarith, by linarith⟩
  unfold Config.lam
  linarith [rimWidth_pos P]

/-! ### The domain `Ω₁` -/

/-- The comparison domain `Ω₁ = {0 < s < τ, A√s < y < h}`. -/
def rimOuter : Set (E d × ℝ) :=
  {q | 0 < C.tstar - q.2 ∧ C.tstar - q.2 < rimTime P ∧
    aperture P * √(C.tstar - q.2) < ‖q.1 - C.xstar‖ - P.ℓ ∧ ‖q.1 - C.xstar‖ - P.ℓ < rimWidth P}

theorem isOpen_rimOuter : IsOpen (rimOuter C) :=
  (isOpen_lt continuous_const (continuous_rimS C)).inter
    ((isOpen_lt (continuous_rimS C) continuous_const).inter
      ((isOpen_lt (continuous_rimWall C) (continuous_rimY C)).inter
        (isOpen_lt (continuous_rimY C) continuous_const)))

theorem closure_rimOuter_subset : closure (rimOuter C) ⊆
    {q | 0 ≤ C.tstar - q.2 ∧ C.tstar - q.2 ≤ rimTime P ∧
      aperture P * √(C.tstar - q.2) ≤ ‖q.1 - C.xstar‖ - P.ℓ ∧
        ‖q.1 - C.xstar‖ - P.ℓ ≤ rimWidth P} :=
  closure_minimal (fun _ hq ↦ ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩)
    ((isClosed_le continuous_const (continuous_rimS C)).inter
      ((isClosed_le (continuous_rimS C) continuous_const).inter
        ((isClosed_le (continuous_rimWall C) (continuous_rimY C)).inter
          (isClosed_le (continuous_rimY C) continuous_const))))

theorem isBounded_rimOuter : Bornology.IsBounded (rimOuter C) := by
  refine ((isBounded_closedBall (x := C.xstar) (r := P.ℓ + rimWidth P)).prod
    (Metric.isBounded_Icc (C.tstar - rimTime P) C.tstar)).subset fun q hq ↦ ?_
  obtain ⟨h1, h2, -, h4⟩ := hq
  exact ⟨by rw [mem_closedBall, dist_eq_norm]; linarith, by linarith, by linarith⟩

theorem closure_rimOuter_near {q : E d × ℝ} (hq : q ∈ closure (rimOuter C)) :
    ‖q.1 - C.xstar‖ < P.lam ∧ C.tstar - 2 * P.μ < q.2 ∧ q.2 ≤ C.tstar := by
  obtain ⟨h1, h2, -, h4⟩ := closure_rimOuter_subset C hq
  exact rim_near C h1 h2 h4

/-- Points with `0 ≤ s < τ`, `A√s < y < h` lie in `Ω̄₁` (for `s = 0` as limits from below). -/
theorem mem_closure_rimOuter {q : E d × ℝ} (hs0 : 0 ≤ C.tstar - q.2)
    (hsτ : C.tstar - q.2 < rimTime P)
    (hAy : aperture P * √(C.tstar - q.2) < ‖q.1 - C.xstar‖ - P.ℓ)
    (hyh : ‖q.1 - C.xstar‖ - P.ℓ < rimWidth P) : q ∈ closure (rimOuter C) := by
  rcases hs0.lt_or_eq with hs | hs
  · exact subset_closure ⟨hs, hsτ, hAy, hyh⟩
  · have hA := aperture_pos P
    set y := ‖q.1 - C.xstar‖ - P.ℓ with hydef
    rw [← hs, Real.sqrt_zero, mul_zero] at hAy
    have hτ : 0 < rimTime P := by linarith
    refine mem_closure_of_forall_sub (δ := min (rimTime P) ((y / aperture P) ^ 2))
      (lt_min hτ (by positivity)) fun ε hε ↦ ?_
    have e1 : C.tstar - (q.2 - ε) = ε := by linarith
    change 0 < C.tstar - (q.2 - ε) ∧ C.tstar - (q.2 - ε) < rimTime P ∧
      aperture P * √(C.tstar - (q.2 - ε)) < y ∧ y < rimWidth P
    rw [e1]
    refine ⟨hε.1, hε.2.trans_le (min_le_left _ _), ?_, hyh⟩
    have h1 : √ε < y / aperture P := by
      calc √ε < √((y / aperture P) ^ 2) :=
            Real.sqrt_lt_sqrt hε.1.le (hε.2.trans_le (min_le_right _ _))
        _ = y / aperture P := Real.sqrt_sq (by positivity)
    calc aperture P * √ε < aperture P * (y / aperture P) := mul_lt_mul_of_pos_left h1 hA
      _ = y := by field_simp

/-! ### Step 2: the comparison -/

/-- The comparison step: there is `κ > 0` with `κ û ≤ b₊` on `Ω̄₁`. Only `û = 0` on the sausage
(which does not use `ν¹ = e_t`) enters. -/
theorem outer_comparison (hd : 1 ≤ d) : ∃ κ : ℝ, 0 < κ ∧ ∀ q ∈ closure (rimOuter C),
    κ * P.uhat q ≤ polarOuterRadial (aperture P) P.ℓ C.tstar C.xstar q := by
  have hA := aperture_pos P
  have hA1 := aperture_le_one P
  have hh := rimWidth_pos P
  have hτ := rimTime_pos P hd
  have hμ := P.μ_pos
  obtain ⟨hbc, hbnd, -, hbsm, hbheat⟩ :=
    polar_barrier_outer (tstar := C.tstar) (xstar := C.xstar) hA hA1 P.ℓ_pos
  obtain ⟨M, hM⟩ := P.isCompact_D.bddAbove_image P.continuousOn_uhat
  have hMu : ∀ p ∈ P.D, P.uhat p ≤ max M 0 := fun p hp ↦
    (hM ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  -- the constant `z_τ = R_b(τ) - A √τ`
  set R := √(P.μ ^ 2 - (P.μ - rimTime P) ^ 2) with hR
  have hAR : aperture P * √(rimTime P) < R := by
    rw [hR, Real.lt_sqrt (by positivity)]
    have := aperture_sqrt_lt P hτ le_rfl
    linarith
  set m := min (rimWidth P / 2) (R - aperture P * √(rimTime P)) with hm
  have hm0 : 0 < m := lt_min (by positivity) (by linarith)
  set κ := m ^ (1 + aperture P / 8) / (max M 0 + 1) with hκdef
  have hκ : 0 < κ := by positivity
  refine ⟨κ, hκ, ?_⟩
  have hsubD : closure (rimOuter C) ⊆ P.D := fun q hq ↦
    have h := closure_rimOuter_near C hq
    mem_D_of_near C h.1 h.2.1 h.2.2
  have hsubU : rimOuter C ⊆ U ×ˢ Ioc 0 T := fun q hq ↦
    have h := closure_rimOuter_near C (subset_closure hq)
    mem_prod_of_near C h.1 h.2.1 h.2.2
  have hG : rimOuter C ⊆ polarOuterDomain (aperture P) P.ℓ C.tstar C.xstar := by
    rintro q ⟨h1, h2, h3, -⟩
    refine ⟨h1, h2.trans_le (rimTime_le_domain P), ?_, h3⟩
    have : 0 ≤ aperture P * √(C.tstar - q.2) := by positivity
    linarith [P.ℓ_pos]
  have hcomp := Heat.domain_comparison_sub (T₁ := C.tstar)
    (b := polarOuterRadial (aperture P) P.ℓ C.tstar C.xstar) (W := κ • P.uhat)
    (isOpen_rimOuter C) (isBounded_rimOuter C) (fun p hp ↦ by linarith [hp.1])
    (((P.isSubcal_hat.restrict hsubU (isOpen_rimOuter C).isParOpen).smul hκ).isCaloricSub)
    ((P.continuousOn_uhat.mono hsubD).const_smul κ) hbc.continuousOn (hbsm.mono hG)
    (fun p hp ↦ hbheat p (hG hp)) ?_
  · exact fun q hq ↦ by simpa using hcomp q hq
  intro p hp hpt
  have hpcl : p ∈ closure (rimOuter C) := frontier_subset_closure hp
  have hpn : p ∉ rimOuter C := by rw [(isOpen_rimOuter C).frontier_eq] at hp; exact hp.2
  obtain ⟨-, hsτ, hAy, hyh⟩ := closure_rimOuter_subset C hpcl
  have hs : 0 < C.tstar - p.2 := by linarith
  have hb0 := (hbnd p hAy).1
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hS : p ∈ sausage C
  · rw [uhat_eq_zero_of_mem_sausage C hS, mul_zero]
    exact (Real.rpow_nonneg (by linarith) _).trans hb0
  have hwall : aperture P * √(C.tstar - p.2) < ‖p.1 - C.xstar‖ - P.ℓ := by
    by_contra hle
    rw [not_lt] at hle
    exact hS (mem_sausage_of_y_le C hle (by positivity) (aperture_sqrt_lt P hs hsτ))
  have hz : m ≤ ‖p.1 - C.xstar‖ - P.ℓ - aperture P * √(C.tstar - p.2) := by
    by_cases hyh' : ‖p.1 - C.xstar‖ - P.ℓ < rimWidth P
    · have hsτ' : C.tstar - p.2 = rimTime P := by
        by_contra hne
        exact hpn ⟨hs, lt_of_le_of_ne hsτ hne, hwall, hyh'⟩
      have hy0 : 0 ≤ ‖p.1 - C.xstar‖ - P.ℓ :=
        le_trans (by positivity : (0 : ℝ) ≤ aperture P * √(C.tstar - p.2)) hwall.le
      have hyR : R ≤ ‖p.1 - C.xstar‖ - P.ℓ := by
        have hnS : ¬ (max (‖p.1 - C.xstar‖ - P.ℓ) 0 ^ 2 + (p.2 - (C.tstar - P.μ)) ^ 2 <
            P.μ ^ 2) := hS
        rw [max_eq_left hy0, not_lt] at hnS
        calc R ≤ √((‖p.1 - C.xstar‖ - P.ℓ) ^ 2) := by
              refine Real.sqrt_le_sqrt ?_
              have : p.2 - (C.tstar - P.μ) = P.μ - rimTime P := by linarith
              rw [this] at hnS
              linarith
          _ = ‖p.1 - C.xstar‖ - P.ℓ := Real.sqrt_sq hy0
      rw [hsτ']
      exact (min_le_right _ _).trans (by linarith)
    · rw [not_lt] at hyh'
      have := aperture_sqrt_le P hsτ
      exact (min_le_left _ _).trans (by linarith)
  calc κ * P.uhat p ≤ κ * max M 0 := mul_le_mul_of_nonneg_left (hMu p (hsubD hpcl)) hκ.le
    _ ≤ m ^ (1 + aperture P / 8) := by
        rw [hκdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        have : 0 ≤ m ^ (1 + aperture P / 8) := by positivity
        nlinarith
    _ ≤ (‖p.1 - C.xstar‖ - P.ℓ - aperture P * √(C.tstar - p.2)) ^ (1 + aperture P / 8) :=
        Real.rpow_le_rpow hm0.le hz (by positivity)
    _ ≤ _ := hb0

/-! ### The proposition -/

/-- At a contact point, the interior normal is not the north pole: `ν¹ ≠ e_t`. -/
theorem no_north_interior (C : ContactData P) : C.ν₁ ≠ ((0 : E d), (1 : ℝ)) := by
  intro hν
  obtain ⟨xb, hxb, hxbE⟩ := exists_rim_mem C hν
  have hd := one_le_d_of_norm_eq P.ℓ_pos hxb
  obtain ⟨κ, hκ, hcomp⟩ := outer_comparison C hd
  have hA := aperture_pos P
  have hA1 := aperture_le_one P
  have hh := rimWidth_pos P
  have hh2 := rimWidth_le_μ P
  have hτ := rimTime_pos P hd
  have hτμ := rimTime_le_μ P
  have hμ := P.μ_pos
  have hc₁ := C.c₁_pos
  obtain ⟨-, hbnd, -⟩ :=
    polar_barrier_outer (tstar := C.tstar) (xstar := C.xstar) hA hA1 P.ℓ_pos
  -- Step 3: the constants `β`, `η`, `ς`, `τ'`
  set ϑ := aperture P / 8 with hϑdef
  have hϑ : 0 < ϑ := by positivity
  set β := C.c₁ / 2 with hβ
  have hβ0 : 0 < β := by positivity
  set η := (κ * β) ^ ϑ⁻¹ with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos (by positivity) _
  have hηϑ : η ^ ϑ = κ * β := Real.rpow_inv_rpow (by positivity) hϑ.ne'
  set ς := min (rimWidth P / 2) (η / 2) with hςdef
  set τ' := min (rimTime P / 2) ((η / 2) ^ 2) with hτ'def
  have hς0 : 0 < ς := lt_min (by positivity) (by positivity)
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by positivity)
  have hςh : ς ≤ rimWidth P / 2 := min_le_left _ _
  have hςη : ς ≤ η / 2 := min_le_right _ _
  have hτ'τ : τ' ≤ rimTime P / 2 := min_le_left _ _
  have hsqrtτ' : √τ' ≤ η / 2 := by
    calc √τ' ≤ √((η / 2) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = η / 2 := Real.sqrt_sq (by positivity)
  set N := closedBall xb ς ×ˢ Icc (C.tstar - τ') C.tstar with hNdef
  have hN : ∀ q ∈ N, |‖q.1 - C.xstar‖ - P.ℓ| ≤ ς ∧ 0 ≤ C.tstar - q.2 ∧ C.tstar - q.2 ≤ τ' := by
    rintro q ⟨hq1, hq2⟩
    rw [mem_closedBall, dist_eq_norm] at hq1
    have := abs_norm_sub_norm_le (q.1 - C.xstar) (xb - C.xstar)
    rw [sub_sub_sub_cancel_right, hxb] at this
    exact ⟨this.trans hq1, by linarith [hq2.2], by linarith [hq2.1]⟩
  have hNO : N ⊆ C.O := fun q hq ↦ by
    obtain ⟨h1, h2, h3⟩ := hN q hq
    have h1' := (abs_le.1 h1).2
    refine mem_O_of_near C ?_ (by linarith) (by linarith)
    unfold Config.lam
    linarith
  -- (i) `E ∩ N ⊆ {|x - x⋆| ≥ λ₁}`
  have hEN : ∀ q ∈ Eset ∩ N, P.ℓ ≤ ‖q.1 - C.xstar‖ := by
    rintro q ⟨hqE, hqN⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨-, hs0, hsτ'⟩ := hN q hqN
    rcases hs0.lt_or_eq with hs | hs
    · exact not_mem_of_mem_sausage C (mem_sausage_of_le C hlt.le hs (by linarith)) hqE
    · exact not_mem_of_mem_topDisk C
        ⟨by rwa [mem_ball, dist_eq_norm], mem_singleton_iff.2 (by linarith)⟩ hqE
  refine slope_sub_static C.touchSub_hat (xb := xb) (z₀ := C.xstar) (tb := C.tstar)
    (by rw [hxb]; exact P.ℓ_pos) hς0 hτ'0 hNO hβ0.le (by linarith)
    (fun q hq ↦ by rw [hxb]; exact hEN q hq) ?_
    (P.uhat_nonneg (mem_D_of_near C (by rw [hxb]; exact P.ℓ_lt_lam) (by linarith) le_rfl))
    hxbE
  -- (ii) `û ≤ β (|x - x⋆| - λ₁)₊` on `E ∩ N`
  rintro q ⟨hqE, hqN⟩
  rw [hxb]
  obtain ⟨hy, hs0, hsτ'⟩ := hN q hqN
  have hy0 : 0 ≤ ‖q.1 - C.xstar‖ - P.ℓ := sub_nonneg.2 (hEN q ⟨hqE, hqN⟩)
  rw [max_eq_left hy0]
  have hyς := (abs_le.1 hy).2
  by_cases hAy : aperture P * √(C.tstar - q.2) < ‖q.1 - C.xstar‖ - P.ℓ
  · have hcl : q ∈ closure (rimOuter C) :=
      mem_closure_rimOuter C hs0 (by linarith) hAy (by linarith)
    have h1 := hcomp q hcl
    have h2 := (hbnd q hAy.le).2
    have h3 : (‖q.1 - C.xstar‖ - P.ℓ + √(C.tstar - q.2)) ^ ϑ ≤ η ^ ϑ := by
      refine Real.rpow_le_rpow (by positivity) ?_ hϑ.le
      have : √(C.tstar - q.2) ≤ √τ' := Real.sqrt_le_sqrt hsτ'
      linarith
    have h4 : κ * P.uhat q ≤ κ * (β * (‖q.1 - C.xstar‖ - P.ℓ)) := by
      calc κ * P.uhat q ≤ _ := h1
        _ ≤ _ := h2
        _ ≤ (‖q.1 - C.xstar‖ - P.ℓ) * η ^ ϑ := mul_le_mul_of_nonneg_left h3 hy0
        _ = κ * (β * (‖q.1 - C.xstar‖ - P.ℓ)) := by rw [hηϑ]; ring
    exact le_of_mul_le_mul_left h4 hκ
  · rw [not_lt] at hAy
    rcases hs0.lt_or_eq with hs | hs
    · exact absurd hqE (not_mem_of_mem_sausage C
        (mem_sausage_of_y_le C hAy (by positivity) (aperture_sqrt_lt P hs (by linarith))))
    · rw [← hs, Real.sqrt_zero, mul_zero] at hAy
      have hq : q = (q.1, C.tstar) := Prod.ext rfl (by linarith)
      have hu0 : P.uhat q = 0 := by
        rw [hq]; exact uhat_eq_zero_of_norm_le C (by linarith)
      rw [hu0]
      exact mul_nonneg hβ0.le hy0

end Polar

end BernoulliComparison
