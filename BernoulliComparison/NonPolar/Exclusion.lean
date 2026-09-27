/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.NonPolar.AxisRate
public import BernoulliComparison.NonPolar.SubRate

/-!
# No doubly non-polar contact

At the contact point, `ν¹ₓ = 0` or `ν²ₓ = 0` (`NonPolar.no_nonpolar`).

Proof: if both are nonzero, put `e = ν¹ₓ/|ν¹ₓ|`. The axis points `z_k = (x⋆ + k e, t⋆)` lie in
`E₁` for small `k > 0` (`axis_mem_E₁`), so `u₁(z_k) ≤ v₁(z_k)` (first crossing). With
`δ' = (c₁ - c₂)/2` and `ε = δ'/c₁`, so that `(1 - ε) c₁ = c₂ + δ'`: `sub_rate` gives
`(c₂ + δ') k < u₁(z_k)` for all small `k`, and `axis_rate` gives arbitrarily small `k` with
`v₁(z_k) < (c₂ + δ') k`. This contradicts `u₁(z_k) ≤ v₁(z_k)`; the contradiction needs the strict
gap `c₂ < c₁` between the local constants of the two touching classes (for `c₁ = c₂` the two rates
would be compatible).

Differences with Kim (2003) (I. C. Kim, *A free boundary problem arising in flame propagation*,
J. Differential Equations 191 (2003), 470–489): Kim uses that the spatial normals are opposite,
`ν¹ₓ/|ν¹ₓ| = -ν²ₓ/|ν²ₓ|`, to transfer the rate of the supersolution along their common direction;
since `axis_rate` holds in every unit direction, collinearity is not needed here. Kim obtains the
strict inequality between the two rates from Hopf's lemma; here it comes from the gap `c₂ < c₁`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace NonPolar

open Contact Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset}

/-- No doubly non-polar contact: `ν¹ₓ = 0` or `ν²ₓ = 0`.

The hypothesis `1 ≤ d` is not used (for `d = 0` the conclusion is trivial anyway). -/
theorem no_nonpolar (_hd : 1 ≤ d) (C : ContactData P) : C.ν₁.1 = 0 ∨ C.ν₂.1 = 0 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have hμ := P.μ_pos
  have hc₁ := C.c₁_pos
  have hgap := C.c₂_lt_c₁
  have hc₂ := C.c₂_pos
  set e : E d := ‖C.ν₁.1‖⁻¹ • C.ν₁.1 with he
  have hnorm : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h₁)]
  set δ' := (C.c₁ - C.c₂) / 2 with hδ'
  have hδ'pos : 0 < δ' := by rw [hδ']; linarith
  set ε := δ' / C.c₁ with hε
  have hε0 : 0 < ε := div_pos hδ'pos hc₁
  have hε1 : ε < 1 := by rw [hε, div_lt_one hc₁, hδ']; linarith
  have hrate : (1 - ε) * C.c₁ = C.c₂ + δ' := by
    rw [hε, sub_mul, one_mul, div_mul_cancel₀ _ hc₁.ne', hδ']; ring
  obtain ⟨k₀, hk₀, hsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset.1 (sub_rate C h₁ hε0 hε1))
  have hk₀' : 0 < k₀ := hk₀
  set a := ‖C.ν₁.1‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 h₁
  set k₁ := min (k₀ / 2) (min (2 * P.μ * a) (2 * P.r₀)) with hk₁
  have hk₁pos : 0 < k₁ := lt_min (by linarith) (lt_min (by positivity) (by linarith [P.r₀_pos]))
  obtain ⟨k, ⟨hk0, hkk₁⟩, hv⟩ := axis_rate C h₂ hnorm hδ'pos hk₁pos
  have hkk₀ : k < k₀ := by linarith [min_le_left (k₀ / 2) (min (2 * P.μ * a) (2 * P.r₀))]
  have hk2 : k ≤ 2 * P.μ * a := hkk₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hk3 : k ≤ 2 * P.r₀ := hkk₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu : (1 - ε) * C.c₁ * k < P.u₁ (C.xstar + k • e, C.tstar) := hsub ⟨hk0, hkk₀⟩
  have hE := axis_mem_E₁ C h₁ hk0.le hk2 hk3
  have hle := C.le_of_eq _ hE rfl
  rw [hrate] at hu
  linarith

end NonPolar

end BernoulliComparison
