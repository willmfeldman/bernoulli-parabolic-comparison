/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Polar.NorthInterior

/-!
# The exterior north pole (N2)

At a contact point, the exterior normal is not the north pole: `ν² ≠ e_t`
(`no_north_exterior`).

Proof. Suppose `ν² = e_t` and let `p₂ = (x̄, t⋆)`, `|x̄ - x⋆| = λ₁`, `v̂(p₂) = 0`, be the
rim zero given by `exists_rim_zero`. In rim coordinates `y = |x - x⋆| - λ₁`, `s = t⋆ - t`:

1. (domain) `Ω₂ = {0 < s < τ, -h < y < A√s}` (`rimInner`) is open, bounded, lies below `t⋆`,
   inside the sausage (so `v̂ > 0` there, `vhat_pos_of_mem_sausage`) and in the domain `G₋` of
   the inner barrier `b₋` (`Barriers.polar_barrier_inner`);
2. (comparison, `inner_comparison`) `b₋ ≤ κ v̂` on `Ω̄₂` for some `κ > 0`, by
   `Heat.domain_comparison_super`: `b₋ = 0` on the side `y = A√s`, and on the compact faces
   `F_lat = {ρ = λ₁ - h, 0 ≤ s ≤ τ}`, `F_bot = {s = τ, -h ≤ y ≤ A√τ}` (where `v̂ ≥ σ₀ > 0`,
   since `v̂ > 0` on `𝒮 ∪ 𝒟`) `b₋ ≤ w^{1-ϑ} ≤ (A√τ + h)^{1-ϑ} = κ σ₀`;
3. (slope bound near `p₂`) `v̂ ≥ 2c₂ (λ₁ - |x - x⋆|)₊` on `N = B̄_ς(x̄) × [t⋆ - τ', t⋆]`, from
   `b₋ ≥ w Π^{-ϑ}`;
4. `Barriers.slope_super` (with `M = 0`) gives `v̂(p₂) > 0`, a contradiction.

The comparison is written as `b₋ ≤ κ v̂`, which is `K b₋ ≤ v̂` with `K = 1/κ`. The hypothesis
`d ≥ 1` is not needed: the rim zero forces it.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Polar

open Crossing Config Contact Barriers

variable {d : ℕ}

/-- A continuous function which is positive on a compact set has a positive lower bound there. -/
theorem exists_pos_le_of_isCompact {F : Set (E d × ℝ)} {f : E d × ℝ → ℝ} (hF : IsCompact F)
    (hf : ContinuousOn f F) (hpos : ∀ p ∈ F, 0 < f p) : ∃ σ : ℝ, 0 < σ ∧ ∀ p ∈ F, σ ≤ f p := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun _ hp ↦ hp.elim⟩
  · obtain ⟨p₀, hp₀, hmin⟩ := hF.exists_isMinOn hne hf
    exact ⟨f p₀, hpos p₀ hp₀, fun p hp ↦ hmin hp⟩

variable {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset} (C : ContactData P)

theorem rimTime_nonneg : 0 ≤ rimTime P :=
  le_min (by linarith [P.μ_pos]) (le_min (sq_nonneg _) (sq_nonneg _))

/-! ### The domain `Ω₂` -/

/-- The comparison domain `Ω₂ = {0 < s < τ, -h < y < A√s}`. -/
def rimInner : Set (E d × ℝ) :=
  {q | 0 < C.tstar - q.2 ∧ C.tstar - q.2 < rimTime P ∧
    -rimWidth P < ‖q.1 - C.xstar‖ - P.ℓ ∧ ‖q.1 - C.xstar‖ - P.ℓ < aperture P * √(C.tstar - q.2)}

theorem isOpen_rimInner : IsOpen (rimInner C) :=
  (isOpen_lt continuous_const (continuous_rimS C)).inter
    ((isOpen_lt (continuous_rimS C) continuous_const).inter
      ((isOpen_lt continuous_const (continuous_rimY C)).inter
        (isOpen_lt (continuous_rimY C) (continuous_rimWall C))))

theorem closure_rimInner_subset : closure (rimInner C) ⊆
    {q | 0 ≤ C.tstar - q.2 ∧ C.tstar - q.2 ≤ rimTime P ∧
      -rimWidth P ≤ ‖q.1 - C.xstar‖ - P.ℓ ∧
        ‖q.1 - C.xstar‖ - P.ℓ ≤ aperture P * √(C.tstar - q.2)} :=
  closure_minimal (fun _ hq ↦ ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩)
    ((isClosed_le continuous_const (continuous_rimS C)).inter
      ((isClosed_le (continuous_rimS C) continuous_const).inter
        ((isClosed_le continuous_const (continuous_rimY C)).inter
          (isClosed_le (continuous_rimY C) (continuous_rimWall C)))))

theorem isBounded_rimInner : Bornology.IsBounded (rimInner C) := by
  refine ((isBounded_closedBall (x := C.xstar) (r := P.ℓ + rimWidth P)).prod
    (Metric.isBounded_Icc (C.tstar - rimTime P) C.tstar)).subset fun q hq ↦ ?_
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have := aperture_sqrt_le P h2.le
  have := rimWidth_pos P
  refine ⟨?_, by linarith, by linarith⟩
  rw [mem_closedBall, dist_eq_norm]; linarith

theorem closure_rimInner_near {q : E d × ℝ} (hq : q ∈ closure (rimInner C)) :
    ‖q.1 - C.xstar‖ < P.lam ∧ C.tstar - 2 * P.μ < q.2 ∧ q.2 ≤ C.tstar := by
  obtain ⟨h1, h2, -, h4⟩ := closure_rimInner_subset C hq
  have := aperture_sqrt_le P h2
  have := rimWidth_pos P
  exact rim_near C h1 h2 (by linarith)

/-- `Ω₂ ⊆ 𝒮`. -/
theorem rimInner_subset_sausage : rimInner C ⊆ sausage C := fun _ hq ↦
  mem_sausage_of_y_le C hq.2.2.2.le (by have := aperture_pos P; positivity)
    (aperture_sqrt_lt P hq.1 hq.2.1.le)

/-- Points with `0 ≤ s < τ`, `-h < y < 0` lie in `Ω̄₂` (for `s = 0` as limits from below). -/
theorem mem_closure_rimInner {q : E d × ℝ} (hs0 : 0 ≤ C.tstar - q.2)
    (hsτ : C.tstar - q.2 < rimTime P) (hhy : -rimWidth P < ‖q.1 - C.xstar‖ - P.ℓ)
    (hy : ‖q.1 - C.xstar‖ - P.ℓ < 0) : q ∈ closure (rimInner C) := by
  have hA := aperture_pos P
  rcases hs0.lt_or_eq with hs | hs
  · exact subset_closure ⟨hs, hsτ, hhy, hy.trans (mul_pos hA (Real.sqrt_pos.2 hs))⟩
  · refine mem_closure_of_forall_sub (δ := rimTime P) (by linarith) fun ε hε ↦ ?_
    have e1 : C.tstar - (q.2 - ε) = ε := by linarith
    change 0 < C.tstar - (q.2 - ε) ∧ C.tstar - (q.2 - ε) < rimTime P ∧
      -rimWidth P < ‖q.1 - C.xstar‖ - P.ℓ ∧
        ‖q.1 - C.xstar‖ - P.ℓ < aperture P * √(C.tstar - (q.2 - ε))
    rw [e1]
    have : 0 < aperture P * √ε := mul_pos hA (Real.sqrt_pos.2 hε.1)
    exact ⟨hε.1, hε.2, hhy, by linarith⟩

/-! ### The faces `F_lat ∪ F_bot` -/

/-- The lateral and bottom faces `F_lat ∪ F_bot` of the comparison domain `Ω₂`. -/
def rimFaces : Set (E d × ℝ) :=
  {q | ‖q.1 - C.xstar‖ = P.ℓ - rimWidth P ∧ 0 ≤ C.tstar - q.2 ∧ C.tstar - q.2 ≤ rimTime P} ∪
    {q | C.tstar - q.2 = rimTime P ∧ -rimWidth P ≤ ‖q.1 - C.xstar‖ - P.ℓ ∧
      ‖q.1 - C.xstar‖ - P.ℓ ≤ aperture P * √(rimTime P)}

theorem rimFaces_bound {q : E d × ℝ} (hq : q ∈ rimFaces C) :
    0 ≤ C.tstar - q.2 ∧ C.tstar - q.2 ≤ rimTime P ∧ |‖q.1 - C.xstar‖ - P.ℓ| ≤ rimWidth P := by
  have hh := rimWidth_pos P
  have h0 := rimTime_nonneg (P := P)
  have hAτ := aperture_sqrt_le P (le_refl (rimTime P))
  rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨h2, h3, abs_le.2 ⟨by linarith, by linarith⟩⟩
  · exact ⟨by linarith, h1.le, abs_le.2 ⟨h2, by linarith⟩⟩

theorem isCompact_rimFaces : IsCompact (rimFaces C) := by
  have hcl : IsClosed (rimFaces C) :=
    ((isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_le continuous_const (continuous_rimS C)).inter
        (isClosed_le (continuous_rimS C) continuous_const))).union
    ((isClosed_eq (continuous_rimS C) continuous_const).inter
      ((isClosed_le continuous_const (continuous_rimY C)).inter
        (isClosed_le (continuous_rimY C) continuous_const)))
  refine Metric.isCompact_of_isClosed_isBounded hcl
    (((isBounded_closedBall (x := C.xstar) (r := P.ℓ + rimWidth P)).prod
      (Metric.isBounded_Icc (C.tstar - rimTime P) C.tstar)).subset fun q hq ↦ ?_)
  obtain ⟨h1, h2, h3⟩ := rimFaces_bound C hq
  have h3' := (abs_le.1 h3).2
  refine ⟨?_, by linarith, by linarith⟩
  rw [mem_closedBall, dist_eq_norm]; linarith

theorem rimFaces_near {q : E d × ℝ} (hq : q ∈ rimFaces C) :
    ‖q.1 - C.xstar‖ < P.lam ∧ C.tstar - 2 * P.μ < q.2 ∧ q.2 ≤ C.tstar := by
  obtain ⟨h1, h2, h3⟩ := rimFaces_bound C hq
  exact rim_near C h1 h2 (abs_le.1 h3).2

/-- `v̂ > 0` on `F_lat ∪ F_bot`, since `v̂ > 0` on `𝒮 ∪ 𝒟`. -/
theorem vhat_pos_of_mem_rimFaces (hd : 1 ≤ d) {q : E d × ℝ} (hq : q ∈ rimFaces C) :
    0 < P.vhat q := by
  have hh := rimWidth_pos P
  have hτ := rimTime_pos P hd
  have hτμ := rimTime_le_μ P
  have hμ := P.μ_pos
  have hA := aperture_pos P
  rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rcases h2.lt_or_eq with hs | hs
    · exact vhat_pos_of_mem_sausage C (mem_sausage_of_le C (by linarith) hs (by linarith))
    · refine vhat_pos_of_mem_topDisk C ⟨?_, mem_singleton_iff.2 (by linarith)⟩
      rw [mem_ball, dist_eq_norm]; linarith
  · refine vhat_pos_of_mem_sausage C (mem_sausage_of_y_le C h3 (by positivity) ?_)
    rw [h1]; exact aperture_sqrt_lt P hτ le_rfl

/-! ### Step 2: the comparison -/

/-- The comparison step: there is `κ > 0` with `b₋ ≤ κ v̂` on `Ω̄₂`. Only `v̂ > 0` on `𝒮 ∪ 𝒟`
(which does not use `ν² = e_t`) enters. -/
theorem inner_comparison (hd : 1 ≤ d) : ∃ κ : ℝ, 0 < κ ∧ ∀ q ∈ closure (rimInner C),
    polarInnerRadial (aperture P) P.ℓ C.tstar C.xstar q ≤ κ * P.vhat q := by
  have hA := aperture_pos P
  have hA1 := aperture_le_one P
  have hh := rimWidth_pos P
  have hh2 := rimWidth_le_ℓ P
  have hτ := rimTime_pos P hd
  obtain ⟨hbc, hbnd, -, hbsm, hbheat⟩ :=
    polar_barrier_inner (tstar := C.tstar) (xstar := C.xstar) hA hA1 P.ℓ_pos
  have hFD : rimFaces C ⊆ P.D := fun q hq ↦
    have h := rimFaces_near C hq
    mem_D_of_near C h.1 h.2.1 h.2.2
  obtain ⟨σ, hσ, hσF⟩ := exists_pos_le_of_isCompact (isCompact_rimFaces C)
    (P.continuousOn_vhat.mono hFD) fun q hq ↦ vhat_pos_of_mem_rimFaces C hd hq
  set L := aperture P * √(rimTime P) + rimWidth P with hL
  have hL0 : 0 < L := by positivity
  set κ := L ^ (1 - aperture P / 8) / σ with hκdef
  have hκ : 0 < κ := by positivity
  refine ⟨κ, hκ, ?_⟩
  have hsubD : closure (rimInner C) ⊆ P.D := fun q hq ↦
    have h := closure_rimInner_near C hq
    mem_D_of_near C h.1 h.2.1 h.2.2
  have hsubPos : rimInner C ⊆ posSetP P.vhat (U ×ˢ Ioc 0 T) := fun q hq ↦
    have h := closure_rimInner_near C (subset_closure hq)
    ⟨mem_prod_of_near C h.1 h.2.1 h.2.2,
      vhat_pos_of_mem_sausage C (rimInner_subset_sausage C hq)⟩
  have hG : rimInner C ⊆ polarInnerDomain (aperture P) P.ℓ C.tstar C.xstar := by
    rintro q ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2.trans_le (rimTime_le_domain P), by linarith, h4⟩
  have hcomp := Heat.domain_comparison_super (T₁ := C.tstar)
    (b := polarInnerRadial (aperture P) P.ℓ C.tstar C.xstar) (v := κ • P.vhat)
    (isOpen_rimInner C) (isBounded_rimInner C) (fun p hp ↦ by linarith [hp.1])
    (((P.isSupercal_hat.restrict hsubPos (isOpen_rimInner C).isParOpen).smul hκ).isCaloricSuper)
    ((P.continuousOn_vhat.mono hsubD).const_smul κ)
    (hbc.mono fun q hq ↦ (closure_rimInner_subset C hq).2.2.2) (hbsm.mono hG)
    (fun p hp ↦ hbheat p (hG hp)) ?_
  · exact fun q hq ↦ by simpa using hcomp q hq
  intro p hp hpt
  have hpcl : p ∈ closure (rimInner C) := frontier_subset_closure hp
  have hpn : p ∉ rimInner C := by rw [(isOpen_rimInner C).frontier_eq] at hp; exact hp.2
  obtain ⟨-, hsτ, hhy, hyA⟩ := closure_rimInner_subset C hpcl
  have hs : 0 < C.tstar - p.2 := by linarith
  have hvp := P.vhat_nonneg (hsubD hpcl)
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases hyA.lt_or_eq with hyA' | hyA'
  · -- `p` lies on a face
    have hF : p ∈ rimFaces C := by
      by_cases hhy' : -rimWidth P < ‖p.1 - C.xstar‖ - P.ℓ
      · have hsτ' : C.tstar - p.2 = rimTime P := by
          by_contra hne
          exact hpn ⟨hs, lt_of_le_of_ne hsτ hne, hhy', hyA'⟩
        refine Or.inr ⟨hsτ', hhy, ?_⟩
        rw [← hsτ']; exact hyA
      · exact Or.inl ⟨by linarith, hs.le, hsτ⟩
    have hw : aperture P * √(C.tstar - p.2) - (‖p.1 - C.xstar‖ - P.ℓ) ≤ L := by
      have : √(C.tstar - p.2) ≤ √(rimTime P) := Real.sqrt_le_sqrt hsτ
      have : aperture P * √(C.tstar - p.2) ≤ aperture P * √(rimTime P) :=
        mul_le_mul_of_nonneg_left this hA.le
      linarith
    calc polarInnerRadial (aperture P) P.ℓ C.tstar C.xstar p
        ≤ (aperture P * √(C.tstar - p.2) - (‖p.1 - C.xstar‖ - P.ℓ)) ^ (1 - aperture P / 8) :=
          (hbnd p hyA).2
      _ ≤ L ^ (1 - aperture P / 8) :=
          Real.rpow_le_rpow (by linarith) hw (by linarith)
      _ = κ * σ := by rw [hκdef, div_mul_cancel₀ _ hσ.ne']
      _ ≤ κ * P.vhat p := mul_le_mul_of_nonneg_left (hσF p hF) hκ.le
  · -- `p` lies on the side `y = A √s`, where `b₋ = 0`
    rw [polarInnerRadial_apply, polarInner, hyA', sub_self, zero_mul]
    exact mul_nonneg hκ.le hvp

/-! ### The proposition -/

/-- At a contact point, the exterior normal is not the north pole: `ν² ≠ e_t`. -/
theorem no_north_exterior (C : ContactData P) : C.ν₂ ≠ ((0 : E d), (1 : ℝ)) := by
  intro hν
  obtain ⟨xb, hxb, hxb0⟩ := exists_rim_zero C hν
  have hd := one_le_d_of_norm_eq P.ℓ_pos hxb
  obtain ⟨κ, hκ, hcomp⟩ := inner_comparison C hd
  have hA := aperture_pos P
  have hA1 := aperture_le_one P
  have hh := rimWidth_pos P
  have hh2 := rimWidth_le_μ P
  have hτ := rimTime_pos P hd
  have hτμ := rimTime_le_μ P
  have hμ := P.μ_pos
  have hc₂ := C.c₂_pos
  -- Step 3: the constants `β`, `η`, `ς`, `τ'`
  set ϑ := aperture P / 8 with hϑdef
  have hϑ : 0 < ϑ := by positivity
  set β := 2 * C.c₂ with hβ
  have hβ0 : 0 < β := by positivity
  set η := (κ * β)⁻¹ ^ ϑ⁻¹ with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos (by positivity) _
  have hηϑ : η ^ (-ϑ) = κ * β := by
    rw [Real.rpow_neg hη.le, hηdef, Real.rpow_inv_rpow (by positivity) hϑ.ne', inv_inv]
  set ς := min (rimWidth P / 2) (η / 3) with hςdef
  set τ' := min (rimTime P / 2) ((η / 3) ^ 2) with hτ'def
  have hς0 : 0 < ς := lt_min (by positivity) (by positivity)
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by positivity)
  have hςh : ς ≤ rimWidth P / 2 := min_le_left _ _
  have hςη : ς ≤ η / 3 := min_le_right _ _
  have hτ'τ : τ' ≤ rimTime P / 2 := min_le_left _ _
  have hsqrtτ' : √τ' ≤ η / 3 := by
    calc √τ' ≤ √((η / 3) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = η / 3 := Real.sqrt_sq (by positivity)
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
  refine (slope_super hc₂ C.touchSuper_hat (xb := xb) (z₀ := C.xstar) (tb := C.tstar)
    (by rw [hxb]; exact P.ℓ_pos) 0 hς0 hτ'0 hNO (by linarith : C.c₂ < β) ?_).ne' hxb0
  -- `v̂ ≥ β (λ₁ - |x - x⋆|)₊` on `N`
  intro q hq
  rw [hxb, zero_mul, sub_zero]
  obtain ⟨hy, hs0, hsτ'⟩ := hN q hq
  have hyς := abs_le.1 hy
  have hqD : q ∈ P.D := by
    have h := rim_near C hs0 (by linarith) (by linarith)
    exact mem_D_of_near C h.1 h.2.1 h.2.2
  by_cases hρ : P.ℓ ≤ ‖q.1 - C.xstar‖
  · rw [max_eq_right (by linarith), mul_zero]
    exact P.vhat_nonneg hqD
  rw [not_le] at hρ
  rw [max_eq_left (by linarith)]
  have hcl : q ∈ closure (rimInner C) :=
    mem_closure_rimInner C hs0 (by linarith) (by linarith) (by linarith)
  have hAs : 0 ≤ aperture P * √(C.tstar - q.2) := by positivity
  have hsq : √(C.tstar - q.2) ≤ √τ' := Real.sqrt_le_sqrt hsτ'
  have hAsq : aperture P * √(C.tstar - q.2) ≤ √τ' := by
    calc aperture P * √(C.tstar - q.2) ≤ 1 * √(C.tstar - q.2) :=
          mul_le_mul_of_nonneg_right hA1 (Real.sqrt_nonneg _)
      _ ≤ √τ' := by rw [one_mul]; exact hsq
  have hPi0 :
      0 < aperture P * √(C.tstar - q.2) - (‖q.1 - C.xstar‖ - P.ℓ) + √(C.tstar - q.2) := by
    have := Real.sqrt_nonneg (C.tstar - q.2)
    linarith
  have hPi :
      aperture P * √(C.tstar - q.2) - (‖q.1 - C.xstar‖ - P.ℓ) + √(C.tstar - q.2) ≤ η := by
    linarith
  have h1 := le_polarInner hA.le (by linarith) hPi0 hPi
  rw [hηϑ] at h1
  have h2 := hcomp q hcl
  rw [polarInnerRadial_apply] at h2
  have h3 : κ * (β * (aperture P * √(C.tstar - q.2) - (‖q.1 - C.xstar‖ - P.ℓ))) ≤
      κ * P.vhat q := by
    calc κ * (β * (aperture P * √(C.tstar - q.2) - (‖q.1 - C.xstar‖ - P.ℓ)))
        = (aperture P * √(C.tstar - q.2) - (‖q.1 - C.xstar‖ - P.ℓ)) * (κ * β) := by ring
      _ ≤ _ := h1
      _ ≤ _ := h2
  have h4 := le_of_mul_le_mul_left h3 hκ
  calc β * (P.ℓ - ‖q.1 - C.xstar‖)
      ≤ β * (aperture P * √(C.tstar - q.2) - (‖q.1 - C.xstar‖ - P.ℓ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hβ0.le
    _ ≤ P.vhat q := h4

end Polar

end BernoulliComparison
