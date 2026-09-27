/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.Data

/-!
# Rim coordinates and the sausage

Standing notation for the polar cases at a contact point `C : ContactData P` with
`p⋆ = (x⋆, t⋆)`, `p̂ = p⋆ - μ e_t`, `λ₁ = P.ℓ`, `λ = P.lam = λ₁ + μ`: for `(x, t)` put
`ρ = |x - x⋆|`, `y = ρ - λ₁`, `s = t⋆ - t` and `R_b(s) = (2μs - s²)^{1/2}`. The sausage and the
top disk are
`𝒮 = {0 < s < 2μ, (ρ - λ₁)₊ < R_b(s)}`, `𝒟 = B_{λ₁}(x⋆) × {t⋆}`.

In Lean the sausage is written without square roots, `(ρ - λ₁)₊² + (t - (t⋆ - μ))² < μ²`
(`sausage`); this is the same set, since `(t - (t⋆ - μ))² < μ²` is `0 < s < 2μ` and
`μ² - (μ - s)² = 2μs - s² = R_b(s)²`.

Constants: `A = min 1 √μ` (`aperture`), `ϑ = A/8`, `h = min λ₁ μ / 2` (`rimWidth`) and
`τ = min (μ/2) (min ((Aλ₁/(16d))²) ((h/(2A))²))` (`rimTime`).

## Main statements

* `sausage_decomp`: every `q ∈ 𝒮` is `p + (e, 0)` with `p ∈ B_μ(p̂)`, `|e| ≤ λ₁`;
* `mem_prod_of_near`, `mem_O_of_near`, `mem_D_of_near`, `sausage_near`: points with `ρ < λ` and
  `0 ≤ s < 2μ` lie in `U × (0, T]`, in `O` and in `D`, and points of `𝒮` satisfy these bounds;
* `aperture_sqrt_lt`, `aperture_sqrt_le`: the parabola `y = A√s` stays inside the sausage and
  within the rim width for `0 < s ≤ τ`;
* `mem_sausage_of_le`, `mem_sausage_of_y_le`: sufficient conditions for membership in `𝒮`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Polar

open Crossing Config Contact

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)}

/-! ### Constants -/

section Constants

variable (P : Config U Q T u v Eset)

/-- The aperture `A = min 1 √μ` of the rim regions. -/
noncomputable def aperture : ℝ := min 1 √P.μ

/-- The rim width `h = min λ₁ μ / 2`. -/
noncomputable def rimWidth : ℝ := min P.ℓ P.μ / 2

/-- The rim time `τ = min (μ/2) (min ((Aλ₁/(16d))²) ((h/(2A))²))`. It is positive
only for `d ≥ 1` (`rimTime_pos`). -/
noncomputable def rimTime : ℝ :=
  min (P.μ / 2) (min ((aperture P * P.ℓ / (16 * d)) ^ 2) ((rimWidth P / (2 * aperture P)) ^ 2))

theorem aperture_pos : 0 < aperture P :=
  lt_min one_pos (Real.sqrt_pos.2 P.μ_pos)

theorem aperture_le_one : aperture P ≤ 1 := min_le_left _ _

theorem aperture_sq_le : aperture P ^ 2 ≤ P.μ := by
  have h1 : aperture P ≤ √P.μ := min_le_right _ _
  have h2 := aperture_pos P
  calc aperture P ^ 2 ≤ √P.μ ^ 2 := pow_le_pow_left₀ h2.le h1 2
    _ = P.μ := Real.sq_sqrt P.μ_pos.le

theorem rimWidth_pos : 0 < rimWidth P := by
  unfold rimWidth; have := lt_min P.ℓ_pos P.μ_pos; linarith

theorem rimWidth_le_ℓ : 2 * rimWidth P ≤ P.ℓ := by
  unfold rimWidth; have := min_le_left P.ℓ P.μ; linarith

theorem rimWidth_le_μ : 2 * rimWidth P ≤ P.μ := by
  unfold rimWidth; have := min_le_right P.ℓ P.μ; linarith

theorem rimTime_pos (hd : 1 ≤ d) : 0 < rimTime P := by
  have hA := aperture_pos P
  have hh := rimWidth_pos P
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have := P.ℓ_pos
  refine lt_min (by linarith [P.μ_pos]) (lt_min ?_ ?_) <;> positivity

theorem rimTime_le_μ : rimTime P ≤ P.μ / 2 := min_le_left _ _

theorem rimTime_le_domain : rimTime P ≤ (aperture P * P.ℓ / (16 * d)) ^ 2 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem rimTime_le_width : rimTime P ≤ (rimWidth P / (2 * aperture P)) ^ 2 :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- `A √s ≤ h/2` for `0 ≤ s ≤ τ`. -/
theorem aperture_sqrt_le {s : ℝ} (hs : s ≤ rimTime P) : aperture P * √s ≤ rimWidth P / 2 := by
  have hA := aperture_pos P
  have hh := rimWidth_pos P
  have h1 : √s ≤ rimWidth P / (2 * aperture P) := by
    calc √s ≤ √((rimWidth P / (2 * aperture P)) ^ 2) :=
          Real.sqrt_le_sqrt (hs.trans (rimTime_le_width P))
      _ = rimWidth P / (2 * aperture P) := Real.sqrt_sq (by positivity)
  calc aperture P * √s ≤ aperture P * (rimWidth P / (2 * aperture P)) :=
        mul_le_mul_of_nonneg_left h1 hA.le
    _ = rimWidth P / 2 := by field_simp

/-- `A √s < R_b(s)` for `0 < s ≤ τ`, in the squared form
`(A √s)² + (μ - s)² < μ²`. -/
theorem aperture_sqrt_lt {s : ℝ} (hs0 : 0 < s) (hs : s ≤ rimTime P) :
    (aperture P * √s) ^ 2 + (P.μ - s) ^ 2 < P.μ ^ 2 := by
  have h1 := aperture_sq_le P
  have h2 := rimTime_le_μ P
  have hμ := P.μ_pos
  rw [mul_pow, Real.sq_sqrt hs0.le]
  nlinarith [mul_le_mul_of_nonneg_right h1 hs0.le]

end Constants

/-! ### The sausage and the top disk -/

variable {P : Config U Q T u v Eset} (C : ContactData P)

/-- The sausage `𝒮 = {(ρ - λ₁)₊ < R_b(s), 0 < s < 2μ}`, written as
`(ρ - λ₁)₊² + (t - (t⋆ - μ))² < μ²`. -/
def sausage : Set (E d × ℝ) :=
  {q | max (‖q.1 - C.xstar‖ - P.ℓ) 0 ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2}

/-- The (open) top disk `𝒟 = B_{λ₁}(x⋆) × {t⋆}`. -/
def topDisk : Set (E d × ℝ) := ball C.xstar P.ℓ ×ˢ {C.tstar}

theorem mem_sausage {q : E d × ℝ} : q ∈ sausage C ↔
    max (‖q.1 - C.xstar‖ - P.ℓ) 0 ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2 :=
  Iff.rfl

/-- Every `q ∈ 𝒮` is `p + (e, 0)` with `p = (q.1 - e, q.2) ∈ B_μ(p̂)` and
`|e| ≤ λ₁` (projection of `q.1 - x⋆` onto the closed disk `B̄_{λ₁}(0)`). -/
theorem sausage_decomp {q : E d × ℝ} (hq : q ∈ sausage C) :
    ∃ e : E d, ‖e‖ ≤ P.ℓ ∧ ((q.1 - e, q.2) : E d × ℝ) ∈ stBallOpen C.phat P.μ := by
  rw [mem_sausage] at hq
  change ∃ e : E d, ‖e‖ ≤ P.ℓ ∧ ‖q.1 - e - C.xstar‖ ^ 2 + (q.2 - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2
  set ρ := ‖q.1 - C.xstar‖ with hρ
  by_cases hle : ρ ≤ P.ℓ
  · refine ⟨q.1 - C.xstar, hle, ?_⟩
    have h0 : max (ρ - P.ℓ) 0 = 0 := max_eq_right (by linarith)
    rw [h0] at hq
    simpa using hq
  · rw [not_le] at hle
    have hρ0 : 0 < ρ := P.ℓ_pos.trans hle
    refine ⟨(P.ℓ / ρ) • (q.1 - C.xstar), ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos P.ℓ_pos hρ0), ← hρ,
        div_mul_cancel₀ _ hρ0.ne']
    · have hmax : max (ρ - P.ℓ) 0 = ρ - P.ℓ := max_eq_left (by linarith)
      rw [hmax] at hq
      have : q.1 - (P.ℓ / ρ) • (q.1 - C.xstar) - C.xstar = (1 - P.ℓ / ρ) • (q.1 - C.xstar) := by
        rw [sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, ← hρ]
      have h1 : 0 ≤ 1 - P.ℓ / ρ := by
        rw [sub_nonneg, div_le_one hρ0]; exact hle.le
      rw [abs_of_nonneg h1, show (1 - P.ℓ / ρ) * ρ = ρ - P.ℓ by field_simp]
      exact hq

/-- Points with `ρ < λ` and `0 ≤ s < 2μ` lie in `U × (0, T]`. -/
theorem mem_prod_of_near {q : E d × ℝ} (hx : ‖q.1 - C.xstar‖ < P.lam)
    (ht1 : C.tstar - 2 * P.μ < q.2) (ht2 : q.2 ≤ C.tstar) : q ∈ U ×ˢ Ioc 0 T := by
  refine ⟨C.closedBall_lam_subset (mem_closedBall.2 (by rw [dist_eq_norm]; exact hx.le)), ?_, ?_⟩
  · linarith [C.two_μ_lt_tstar]
  · exact ht2.trans C.tstar_le_T

/-- Points with `ρ < λ` and `0 ≤ s < 2μ` lie in `O = (W⋆ ∩ U) × (0, T]`. -/
theorem mem_O_of_near {q : E d × ℝ} (hx : ‖q.1 - C.xstar‖ < P.lam)
    (ht1 : C.tstar - 2 * P.μ < q.2) (ht2 : q.2 ≤ C.tstar) : q ∈ C.O := by
  have h := mem_prod_of_near C hx ht1 ht2
  refine ⟨⟨?_, h.1⟩, h.2⟩
  change q.1 ∈ ball C.xstar (2 * P.lam)
  rw [mem_ball, dist_eq_norm]
  linarith [P.lam_pos]

/-- Points with `ρ < λ` and `0 ≤ s < 2μ` lie in `D = Ū × [0, T]`. -/
theorem mem_D_of_near {q : E d × ℝ} (hx : ‖q.1 - C.xstar‖ < P.lam)
    (ht1 : C.tstar - 2 * P.μ < q.2) (ht2 : q.2 ≤ C.tstar) : q ∈ P.D := by
  have h := mem_prod_of_near C hx ht1 ht2
  exact ⟨subset_closure h.1, h.2.1.le, h.2.2⟩

/-- Points of `𝒮` have `ρ < λ` and `0 < s < 2μ`. -/
theorem sausage_near {q : E d × ℝ} (hq : q ∈ sausage C) :
    ‖q.1 - C.xstar‖ < P.lam ∧ C.tstar - 2 * P.μ < q.2 ∧ q.2 < C.tstar := by
  rw [mem_sausage] at hq
  have hμ := P.μ_pos
  have h1 : (q.2 - (C.tstar - P.μ)) ^ 2 < P.μ ^ 2 := by
    nlinarith [sq_nonneg (max (‖q.1 - C.xstar‖ - P.ℓ) 0)]
  have h2 : max (‖q.1 - C.xstar‖ - P.ℓ) 0 ^ 2 < P.μ ^ 2 := by
    nlinarith [sq_nonneg (q.2 - (C.tstar - P.μ))]
  have h1' := abs_lt.1 (abs_lt_of_sq_lt_sq h1 hμ.le)
  have h2' := abs_lt.1 (abs_lt_of_sq_lt_sq h2 hμ.le)
  refine ⟨?_, by linarith, by linarith⟩
  have := le_max_left (‖q.1 - C.xstar‖ - P.ℓ) 0
  unfold Config.lam
  linarith

theorem mem_O_of_mem_sausage {q : E d × ℝ} (hq : q ∈ sausage C) : q ∈ C.O :=
  have h := sausage_near C hq
  mem_O_of_near C h.1 h.2.1 h.2.2.le

theorem mem_D_of_mem_sausage {q : E d × ℝ} (hq : q ∈ sausage C) : q ∈ P.D :=
  have h := sausage_near C hq
  mem_D_of_near C h.1 h.2.1 h.2.2.le

/-- A sufficient condition for `q ∈ 𝒮`: `ρ - λ₁ ≤ a` with `0 ≤ a` and `a² + (μ - s)² < μ²`. -/
theorem mem_sausage_of_y_le {q : E d × ℝ} {a : ℝ} (hy : ‖q.1 - C.xstar‖ - P.ℓ ≤ a) (ha : 0 ≤ a)
    (h : a ^ 2 + (P.μ - (C.tstar - q.2)) ^ 2 < P.μ ^ 2) : q ∈ sausage C := by
  rw [mem_sausage]
  have h1 : max (‖q.1 - C.xstar‖ - P.ℓ) 0 ≤ a := max_le hy ha
  have h2 : 0 ≤ max (‖q.1 - C.xstar‖ - P.ℓ) 0 := le_max_right _ _
  have h3 : (q.2 - (C.tstar - P.μ)) = P.μ - (C.tstar - q.2) := by ring
  rw [h3]
  nlinarith [mul_le_mul h1 h1 h2 ha]

/-- Points with `ρ ≤ λ₁` and `0 < s < 2μ` lie in `𝒮`. -/
theorem mem_sausage_of_le {q : E d × ℝ} (hx : ‖q.1 - C.xstar‖ ≤ P.ℓ) (hs0 : 0 < C.tstar - q.2)
    (hs : C.tstar - q.2 < 2 * P.μ) : q ∈ sausage C := by
  refine mem_sausage_of_y_le C (a := 0) (by linarith) le_rfl ?_
  nlinarith

/-- The closure of the top disk: `𝒟̄ = B̄_{λ₁}(x⋆) × {t⋆}`. -/
theorem closure_topDisk : closure (topDisk C) = closedBall C.xstar P.ℓ ×ˢ {C.tstar} := by
  rw [topDisk, closure_prod_eq, closure_ball _ P.ℓ_pos.ne', closure_singleton]

end Polar

end BernoulliComparison
