/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Setting
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Radial calculus: gradient and Laplacian of `f (ψ x)` and of `f ‖x - z‖`

On a finite-dimensional real inner product space `F`:

* `laplacian_comp_real`: the chain rule for the Laplacian,
  `Δ (f ∘ ψ) = f''(ψ) ‖∇ψ‖² + f'(ψ) Δψ` for `f : ℝ → ℝ` and `ψ : F → ℝ` of class `C²`;
  `gradient_comp_real`: `∇ (f ∘ ψ) = f'(ψ) ∇ψ`;
* `laplacian_norm_sub_sq`, `gradient_norm_sub_sq`: `Δ ‖x - z‖² = 2 dim F`, `∇ ‖x - z‖² = 2 (x - z)`;
* `laplacian_norm_sub`, `gradient_norm_sub`: for `x ≠ z`, `Δ ‖x - z‖ = (dim F - 1) / ‖x - z‖` and
  `∇ ‖x - z‖ = (x - z) / ‖x - z‖`;
* `laplacian_radial`, `gradient_radial`, `norm_gradient_radial`: for `x ≠ z` and `r = ‖x - z‖`,
  `Δ f(‖x - z‖) = f''(r) + (dim F - 1) f'(r) / r` and `|∇ f(‖x - z‖)| = |f'(r)|`.

This is the radial calculus behind the radial barriers of `Barriers/Slope.lean` and
`Barriers/PolarRadial.lean`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian ContDiff RealInnerProductSpace

namespace BernoulliComparison

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Chain rule -/

section Chain

variable {f : ℝ → ℝ} {ψ : F → ℝ} {x : F}

/-- The Laplacian as the trace of the second derivative `fderiv (fderiv ψ)` along an
orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv (ψ : F → ℝ) (x : F) :
    Δ ψ x = ∑ i, fderiv ℝ (fderiv ℝ ψ) x (stdOrthonormalBasis ℝ F i)
      (stdOrthonormalBasis ℝ F i) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_two_apply]

theorem sum_fderiv_sq_eq_norm_gradient_sq (ψ : F → ℝ) (x : F) :
    ∑ i, fderiv ℝ ψ x (stdOrthonormalBasis ℝ F i) * fderiv ℝ ψ x (stdOrthonormalBasis ℝ F i) =
      ‖∇ ψ x‖ ^ 2 := by
  have h : ∀ v : F, fderiv ℝ ψ x v = ⟪∇ ψ x, v⟫ := fun v ↦ by
    simp [gradient, toDual_symm_apply]
  simp_rw [h]
  conv_lhs => enter [2, i, 2]; rw [real_inner_comm]
  rw [(stdOrthonormalBasis ℝ F).sum_inner_mul_inner, real_inner_self_eq_norm_sq]

/-- **Gradient chain rule** `∇ (f ∘ ψ) = f'(ψ) ∇ψ`. -/
theorem gradient_comp_real (hf : DifferentiableAt ℝ f (ψ x)) (hψ : DifferentiableAt ℝ ψ x) :
    ∇ (fun y ↦ f (ψ y)) x = deriv f (ψ x) • ∇ ψ x := by
  have H : HasFDerivAt (fun y ↦ f (ψ y)) (deriv f (ψ x) • fderiv ℝ ψ x) x :=
    hf.hasDerivAt.comp_hasFDerivAt x hψ.hasFDerivAt
  simp only [gradient, H.fderiv, map_smul]

/-- **Laplacian chain rule** `Δ (f ∘ ψ) = f''(ψ) ‖∇ψ‖² + f'(ψ) Δψ`. -/
theorem laplacian_comp_real (hf : ContDiffAt ℝ 2 f (ψ x)) (hψ : ContDiffAt ℝ 2 ψ x) :
    Δ (fun y ↦ f (ψ y)) x =
      deriv (deriv f) (ψ x) * ‖∇ ψ x‖ ^ 2 + deriv f (ψ x) * Δ ψ x := by
  have hψ' : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 ψ y := hψ.eventually (by simp)
  have hf' : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (ψ y) :=
    hψ.continuousAt.eventually (hf.eventually (by simp))
  have hD : fderiv ℝ (fun y ↦ f (ψ y)) =ᶠ[𝓝 x] fun y ↦ deriv f (ψ y) • fderiv ℝ ψ y := by
    filter_upwards [hψ', hf'] with y h1 h2
    exact ((h2.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y
      (h1.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hdf : HasDerivAt (deriv f) (deriv (deriv f) (ψ x)) (ψ x) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) (ψ x) := hf.fderiv_right (by norm_num)
    have h2 : DifferentiableAt ℝ (fun s ↦ fderiv ℝ f s 1) (ψ x) :=
      (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
    exact h2.hasDerivAt
  have hdψ : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
    (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have hprod := (hdf.comp_hasFDerivAt x hψd).smul hdψ
  have hDD : fderiv ℝ (fderiv ℝ fun y ↦ f (ψ y)) x = _ := hD.fderiv_eq.trans hprod.fderiv
  rw [laplacian_eq_sum_fderiv_fderiv, laplacian_eq_sum_fderiv_fderiv, hDD,
    ← sum_fderiv_sq_eq_norm_gradient_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  ring

end Chain

/-! ### The squared distance and the distance -/

section Distance

variable (z : F)

omit [FiniteDimensional ℝ F] in
theorem hasFDerivAt_norm_sub_sq (y : F) :
    HasFDerivAt (fun y : F ↦ ‖y - z‖ ^ 2) (((2 : ℝ) • innerSL ℝ (E := F)) (y - z)) y := by
  refine ((hasFDerivAt_id y).sub_const z).norm_sq.congr_fderiv ?_
  ext v
  simp

omit [FiniteDimensional ℝ F] in
theorem fderiv_norm_sub_sq :
    fderiv ℝ (fun y : F ↦ ‖y - z‖ ^ 2) = fun y ↦ ((2 : ℝ) • innerSL ℝ (E := F)) (y - z) :=
  funext fun y ↦ (hasFDerivAt_norm_sub_sq z y).fderiv

/-- `∇ ‖x - z‖² = 2 (x - z)`. -/
theorem gradient_norm_sub_sq (x : F) : ∇ (fun y : F ↦ ‖y - z‖ ^ 2) x = (2 : ℝ) • (x - z) := by
  refine HasGradientAt.gradient (hasGradientAt_iff_hasFDerivAt.2 ?_)
  convert hasFDerivAt_norm_sub_sq z x using 1
  ext v
  simp [toDual_apply_apply]

/-- `Δ ‖x - z‖² = 2 dim F`. -/
theorem laplacian_norm_sub_sq (x : F) :
    Δ (fun y : F ↦ ‖y - z‖ ^ 2) x = 2 * Module.finrank ℝ F := by
  have H : HasFDerivAt (fun y : F ↦ ((2 : ℝ) • innerSL ℝ (E := F)) (y - z))
      ((2 : ℝ) • innerSL ℝ (E := F)) x := by
    have := ((2 : ℝ) • innerSL ℝ (E := F)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
    rwa [ContinuousLinearMap.comp_id] at this
  rw [laplacian_eq_sum_fderiv_fderiv, fderiv_norm_sub_sq, H.fderiv]
  -- restate to normalize the instance path of the codomain `F →L[ℝ] ℝ`
  change ∑ i, (((2 : ℝ) • innerSL ℝ (E := F)) (stdOrthonormalBasis ℝ F i))
      (stdOrthonormalBasis ℝ F i) = _
  simp
  ring

variable {z}

omit [FiniteDimensional ℝ F] in
theorem contDiffAt_norm_sub {n : WithTop ℕ∞} {x : F} (hx : x ≠ z) :
    ContDiffAt ℝ n (fun y : F ↦ ‖y - z‖) x :=
  (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)

/-- `∇ ‖x - z‖ = (x - z) / ‖x - z‖` for `x ≠ z`. -/
theorem gradient_norm_sub {x : F} (hx : x ≠ z) :
    ∇ (fun y : F ↦ ‖y - z‖) x = ‖x - z‖⁻¹ • (x - z) := by
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hfun : (fun y : F ↦ ‖y - z‖) = fun y ↦ √(‖y - z‖ ^ 2) :=
    funext fun y ↦ (Real.sqrt_sq (norm_nonneg _)).symm
  have hs : ‖x - z‖ ^ 2 ≠ 0 := by positivity
  rw [hfun, gradient_comp_real (f := fun s ↦ √s) (ψ := fun y ↦ ‖y - z‖ ^ 2)
    (Real.hasDerivAt_sqrt hs).differentiableAt
    ((hasFDerivAt_norm_sub_sq z x).differentiableAt), (Real.hasDerivAt_sqrt hs).deriv,
    gradient_norm_sub_sq, Real.sqrt_sq (norm_nonneg _), smul_smul]
  congr 1
  field_simp

theorem norm_gradient_norm_sub {x : F} (hx : x ≠ z) : ‖∇ (fun y : F ↦ ‖y - z‖) x‖ = 1 := by
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  rw [gradient_norm_sub hx, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']

/-- `Δ ‖x - z‖ = (dim F - 1) / ‖x - z‖` for `x ≠ z`. -/
theorem laplacian_norm_sub {x : F} (hx : x ≠ z) :
    Δ (fun y : F ↦ ‖y - z‖) x = ((Module.finrank ℝ F : ℝ) - 1) / ‖x - z‖ := by
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hsq : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ 2) ‖x - z‖ := contDiffAt_id.pow 2
  have H := laplacian_comp_real (f := fun s : ℝ ↦ s ^ 2) (ψ := fun y : F ↦ ‖y - z‖) hsq
    (contDiffAt_norm_sub (n := 2) hx)
  have hd1 : deriv (fun s : ℝ ↦ s ^ 2) = fun s ↦ 2 * s := funext fun s ↦ by simp
  have hd2 : deriv (fun s : ℝ ↦ 2 * s) = fun _ ↦ 2 := funext fun s ↦
    ((hasDerivAt_id' s).const_mul (2 : ℝ)).deriv.trans (mul_one 2)
  rw [hd1, hd2, norm_gradient_norm_sub hx, laplacian_norm_sub_sq] at H
  field_simp
  linarith

end Distance

/-! ### Radial functions -/

section Radial

variable {f : ℝ → ℝ} {x z : F}

/-- **Radial gradient.** `∇ f(‖x - z‖) = f'(r) (x - z) / r`, `r = ‖x - z‖ > 0`. -/
theorem gradient_radial (hf : DifferentiableAt ℝ f ‖x - z‖) (hx : x ≠ z) :
    ∇ (fun y : F ↦ f ‖y - z‖) x = deriv f ‖x - z‖ • ‖x - z‖⁻¹ • (x - z) := by
  rw [gradient_comp_real (ψ := fun y : F ↦ ‖y - z‖) hf
    ((contDiffAt_norm_sub (n := 1) hx).differentiableAt one_ne_zero), gradient_norm_sub hx]

theorem norm_gradient_radial (hf : DifferentiableAt ℝ f ‖x - z‖) (hx : x ≠ z) :
    ‖∇ (fun y : F ↦ f ‖y - z‖) x‖ = |deriv f ‖x - z‖| := by
  rw [gradient_comp_real (ψ := fun y : F ↦ ‖y - z‖) hf
    ((contDiffAt_norm_sub (n := 1) hx).differentiableAt one_ne_zero), norm_smul,
    norm_gradient_norm_sub hx, mul_one, Real.norm_eq_abs]

/-- **Radial Laplacian.** `Δ f(‖x - z‖) = f''(r) + (dim F - 1) f'(r) / r`, `r = ‖x - z‖ > 0`. -/
theorem laplacian_radial (hf : ContDiffAt ℝ 2 f ‖x - z‖) (hx : x ≠ z) :
    Δ (fun y : F ↦ f ‖y - z‖) x =
      deriv (deriv f) ‖x - z‖ +
        ((Module.finrank ℝ F : ℝ) - 1) * deriv f ‖x - z‖ / ‖x - z‖ := by
  rw [laplacian_comp_real (ψ := fun y : F ↦ ‖y - z‖) hf (contDiffAt_norm_sub hx),
    norm_gradient_norm_sub hx,
    laplacian_norm_sub hx]
  ring

end Radial

/-! ### Affine reparametrizations and linear combinations -/

section Affine

theorem deriv_comp_mul_add (f : ℝ → ℝ) (a b : ℝ) :
    deriv (fun r ↦ f (a * r + b)) = fun r ↦ a * deriv f (a * r + b) := by
  funext r
  have := deriv_comp_mul_left (f := fun u ↦ f (u + b)) (c := a) (x := r)
  simp only [smul_eq_mul, deriv_comp_add_const] at this
  exact this

theorem deriv_deriv_comp_mul_add (f : ℝ → ℝ) (a b : ℝ) :
    deriv (deriv fun r ↦ f (a * r + b)) = fun r ↦ a ^ 2 * deriv (deriv f) (a * r + b) := by
  rw [deriv_comp_mul_add]
  funext r
  rw [deriv_const_mul_field', deriv_comp_mul_add]
  ring

theorem contDiffAt_comp_mul_add {n : WithTop ℕ∞} {f : ℝ → ℝ} {a b r : ℝ}
    (hf : ContDiffAt ℝ n f (a * r + b)) : ContDiffAt ℝ n (fun r ↦ f (a * r + b)) r :=
  hf.comp r ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)

/-- `Δ (a g + c) = a Δ g`. -/
theorem laplacian_const_mul_add_const {g : F → ℝ} {x : F} (hg : ContDiffAt ℝ 2 g x) (a c : ℝ) :
    Δ (fun y ↦ a * g y + c) x = a * Δ g x := by
  have H := laplacian_comp_real (f := fun s ↦ a * s + c) (ψ := g)
    (contDiffAt_comp_mul_add (f := id) contDiffAt_id) hg
  have h1 := deriv_comp_mul_add id a c
  have h2 := deriv_deriv_comp_mul_add id a c
  simp only [id] at h1 h2
  rw [H, h2, h1]
  simp

/-- `∇ (a g + c) = a ∇ g`. -/
theorem gradient_const_mul_add_const {g : F → ℝ} {x : F} (hg : DifferentiableAt ℝ g x)
    (a c : ℝ) : ∇ (fun y ↦ a * g y + c) x = a • ∇ g x := by
  have H := gradient_comp_real (f := fun s ↦ a * s + c) (ψ := g)
    ((contDiffAt_comp_mul_add (n := 1) (f := id) contDiffAt_id).differentiableAt one_ne_zero) hg
  have h1 := deriv_comp_mul_add id a c
  simp only [id] at h1
  rw [H, h1]
  simp

end Affine

/-! ### Space-time radial profiles `f(a(t) ‖x - z‖ + b(t))` -/

section SpaceTime

variable {d : ℕ} {f a b : ℝ → ℝ} {z : E d} {p : E d × ℝ}

/-- The space-time radial profile `f(a(t) ‖x - z‖ + b(t))`: dilations (`a`) and translations
(`b`) of a radial profile. -/
noncomputable def radialProfile (f a b : ℝ → ℝ) (z : E d) : E d × ℝ → ℝ :=
  fun q ↦ f (a q.2 * ‖q.1 - z‖ + b q.2)

theorem radialProfile_apply (q : E d × ℝ) :
    radialProfile f a b z q = f (a q.2 * ‖q.1 - z‖ + b q.2) := rfl

theorem isOpen_setOf_fst_ne (z : E d) : IsOpen {q : E d × ℝ | q.1 ≠ z} :=
  isOpen_ne_fun continuous_fst continuous_const

/-- The radial profile is `C^∞` away from the axis `{x = z}`. -/
theorem contDiffOn_radialProfile {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (ha : ContDiff ℝ n a)
    (hb : ContDiff ℝ n b) : ContDiffOn ℝ n (radialProfile f a b z) {q | q.1 ≠ z} := by
  intro q hq
  refine (hf.contDiffAt.comp q ?_).contDiffWithinAt
  refine ((ha.contDiffAt.comp q contDiffAt_snd).mul ?_).add (hb.contDiffAt.comp q contDiffAt_snd)
  exact (contDiffAt_norm_sub (n := n) hq).comp q contDiffAt_fst

/-- **Radial Laplacian in space-time.** With `r = ‖x - z‖ > 0` and `ξ = a(t) r + b(t)`:
`Δₓ f(a(t) ‖x - z‖ + b(t)) = a(t)² f''(ξ) + (d - 1) a(t) f'(ξ) / r`. -/
theorem lapₓ_radialProfile (hf : ContDiffAt ℝ 2 f (a p.2 * ‖p.1 - z‖ + b p.2)) (hx : p.1 ≠ z) :
    lapₓ (radialProfile f a b z) p =
      a p.2 ^ 2 * deriv (deriv f) (a p.2 * ‖p.1 - z‖ + b p.2) +
        ((d : ℝ) - 1) * (a p.2 * deriv f (a p.2 * ‖p.1 - z‖ + b p.2)) / ‖p.1 - z‖ := by
  have H := laplacian_radial (F := E d) (f := fun r ↦ f (a p.2 * r + b p.2))
    (contDiffAt_comp_mul_add hf) hx
  rw [deriv_deriv_comp_mul_add, deriv_comp_mul_add, finrank_euclideanSpace_fin] at H
  exact H

/-- **Radial gradient in space-time.** `∇ₓ f(a(t) ‖x - z‖ + b(t)) = a(t) f'(ξ) (x - z) / r`. -/
theorem gradₓ_radialProfile (hf : DifferentiableAt ℝ f (a p.2 * ‖p.1 - z‖ + b p.2))
    (hx : p.1 ≠ z) :
    gradₓ (radialProfile f a b z) p =
      (a p.2 * deriv f (a p.2 * ‖p.1 - z‖ + b p.2)) • ‖p.1 - z‖⁻¹ • (p.1 - z) := by
  have hl : HasDerivAt (fun r ↦ a p.2 * r + b p.2) (a p.2 * 1) ‖p.1 - z‖ :=
    ((hasDerivAt_id' _).const_mul _).add_const _
  have hf' : DifferentiableAt ℝ (fun r ↦ f (a p.2 * r + b p.2)) ‖p.1 - z‖ :=
    (hf.hasDerivAt.comp (h := fun r ↦ a p.2 * r + b p.2) _ hl).differentiableAt
  have H := gradient_radial (F := E d) hf' hx
  rw [deriv_comp_mul_add] at H
  exact H

theorem norm_gradₓ_radialProfile (hf : DifferentiableAt ℝ f (a p.2 * ‖p.1 - z‖ + b p.2))
    (hx : p.1 ≠ z) :
    ‖gradₓ (radialProfile f a b z) p‖ = |a p.2 * deriv f (a p.2 * ‖p.1 - z‖ + b p.2)| := by
  have hpos : 0 < ‖p.1 - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  rw [gradₓ_radialProfile hf hx, norm_smul, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ hpos.ne', mul_one, Real.norm_eq_abs]

/-- **Time derivative of the radial profile.** `∂ₜ f(a(t) r + b(t)) = f'(ξ) (a'(t) r + b'(t))`. -/
theorem dₜ_radialProfile (hf : DifferentiableAt ℝ f (a p.2 * ‖p.1 - z‖ + b p.2)) {a' b' : ℝ}
    (ha : HasDerivAt a a' p.2) (hb : HasDerivAt b b' p.2) :
    dₜ (radialProfile f a b z) p =
      deriv f (a p.2 * ‖p.1 - z‖ + b p.2) * (a' * ‖p.1 - z‖ + b') := by
  have H : HasDerivAt (fun s ↦ a s * ‖p.1 - z‖ + b s) (a' * ‖p.1 - z‖ + b') p.2 :=
    (ha.mul_const _).add hb
  exact (hf.hasDerivAt.comp p.2 H).deriv

end SpaceTime

end BernoulliComparison
