/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Interface.Setting
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Calculus for the space-time operators `gradₓ`, `lapₓ`, `dₜ`

For a `C²` space-time function `φ : E d × ℝ → ℝ`:

* formulas for `dₜ φ`, `gradₓ φ`, `lapₓ φ` in terms of the (iterated) Fréchet derivatives of `φ`
  (`dₜ_eq_fderiv`, `gradₓ_eq_fderiv`, `lapₓ_eq_iteratedFDeriv`);
* continuity of `dₜ φ`, `gradₓ φ`, `lapₓ φ` (`continuous_dₜ`, `continuous_gradₓ`,
  `continuous_lapₓ`);
* linearity (`dₜ_add`, `dₜ_const_mul`, `dₜ_add_const`, and the same for `gradₓ`, `lapₓ`);
* second-order conditions at a minimum: `laplacian_nonneg_of_isLocalMin` (a `C²` function on a
  finite-dimensional real inner product space has nonnegative Laplacian at a local minimum),
  `lapₓ_nonneg_of_isLocalMin`, `gradₓ_eq_zero_of_isLocalMin`, `dₜ_nonpos_of_isLocalMinOn_Iic`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian ContDiff

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Derivatives of slices -/

section Slices

variable {φ h : E d × ℝ → ℝ}

theorem contDiff_sliceX {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (t : ℝ) :
    ContDiff ℝ n (fun y : E d ↦ φ (y, t)) :=
  hφ.comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_sliceT {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (x : E d) :
    ContDiff ℝ n (fun s : ℝ ↦ φ (x, s)) :=
  hφ.comp (contDiff_const.prodMk contDiff_id)

theorem hasFDerivAt_sliceX (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    HasFDerivAt (fun y : E d ↦ φ (y, q.2))
      ((fderiv ℝ φ q).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) q.1 :=
  (hφ q).hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left q.1 q.2)

theorem hasDerivAt_sliceT (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    HasDerivAt (fun s : ℝ ↦ φ (q.1, s)) (fderiv ℝ φ q (0, 1)) q.2 := by
  have h1 : HasDerivAt (fun s : ℝ ↦ (q.1, s)) ((0 : E d), (1 : ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact (hφ q).hasFDerivAt.comp_hasDerivAt q.2 h1

theorem dₜ_eq_fderiv (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    dₜ φ q = fderiv ℝ φ q (0, 1) :=
  (hasDerivAt_sliceT hφ q).deriv

theorem gradₓ_eq_fderiv (hφ : Differentiable ℝ φ) (q : E d × ℝ) :
    gradₓ φ q = (toDual ℝ (E d)).symm
      ((fderiv ℝ φ q).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) := by
  simp only [gradₓ, gradient, (hasFDerivAt_sliceX hφ q).fderiv]

theorem lapₓ_eq_iteratedFDeriv (hφ : ContDiff ℝ 2 φ) (q : E d × ℝ) :
    lapₓ φ q = ∑ i, iteratedFDeriv ℝ 2 φ q
      ![((stdOrthonormalBasis ℝ (E d)) i, 0), ((stdOrthonormalBasis ℝ (E d)) i, 0)] := by
  have hslice : (fun y : E d ↦ φ (y, q.2)) =
      (fun z : E d × ℝ ↦ φ (z + (0, q.2))) ∘ ContinuousLinearMap.inl ℝ (E d) ℝ := by
    funext y; simp
  have hshift : ContDiff ℝ 2 (fun z : E d × ℝ ↦ φ (z + (0, q.2))) :=
    hφ.comp (contDiff_id.add contDiff_const)
  simp only [lapₓ, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hslice, ContinuousLinearMap.iteratedFDeriv_comp_right _ hshift _ le_rfl,
    iteratedFDeriv_comp_add_right']
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  · simp
  · ext j <;> fin_cases j <;> simp

/-! ### Continuity -/

theorem continuous_dₜ (hφ : ContDiff ℝ 1 φ) : Continuous (dₜ φ) := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have : dₜ φ = fun q ↦ fderiv ℝ φ q (0, 1) := funext (dₜ_eq_fderiv hd)
  rw [this]
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_gradₓ (hφ : ContDiff ℝ 1 φ) : Continuous (gradₓ φ) := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have : gradₓ φ = fun q ↦ (toDual ℝ (E d)).symm
      ((fderiv ℝ φ q).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) := funext (gradₓ_eq_fderiv hd)
  rw [this]
  exact (toDual ℝ (E d)).symm.continuous.comp
    ((hφ.continuous_fderiv one_ne_zero).clm_comp continuous_const)

theorem continuous_lapₓ (hφ : ContDiff ℝ 2 φ) : Continuous (lapₓ φ) := by
  have : lapₓ φ = fun q ↦ ∑ i, iteratedFDeriv ℝ 2 φ q
      ![((stdOrthonormalBasis ℝ (E d)) i, 0), ((stdOrthonormalBasis ℝ (E d)) i, 0)] :=
    funext (lapₓ_eq_iteratedFDeriv hφ)
  rw [this]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (continuous_eval_const _).comp (hφ.continuous_iteratedFDeriv le_rfl)

/-! ### Linearity -/

theorem dₜ_add (hφ : Differentiable ℝ φ) (hh : Differentiable ℝ h) (q : E d × ℝ) :
    dₜ (fun q ↦ φ q + h q) q = dₜ φ q + dₜ h q :=
  ((hasDerivAt_sliceT hφ q).add (hasDerivAt_sliceT hh q)).deriv.trans
    (by rw [dₜ_eq_fderiv hφ, dₜ_eq_fderiv hh])

theorem dₜ_const_mul (hh : Differentiable ℝ h) (a : ℝ) (q : E d × ℝ) :
    dₜ (fun q ↦ a * h q) q = a * dₜ h q :=
  ((hasDerivAt_sliceT hh q).const_mul a).deriv.trans (by rw [dₜ_eq_fderiv hh])

theorem dₜ_add_const (h : E d × ℝ → ℝ) (b : ℝ) (q : E d × ℝ) :
    dₜ (fun q ↦ h q + b) q = dₜ h q := by
  simp [dₜ]

theorem gradₓ_add (hφ : Differentiable ℝ φ) (hh : Differentiable ℝ h) (q : E d × ℝ) :
    gradₓ (fun q ↦ φ q + h q) q = gradₓ φ q + gradₓ h q := by
  have H : HasFDerivAt (fun y : E d ↦ φ (y, q.2) + h (y, q.2)) _ q.1 :=
    (hasFDerivAt_sliceX hφ q).add (hasFDerivAt_sliceX hh q)
  simp only [gradₓ, gradient]
  rw [H.fderiv, (hasFDerivAt_sliceX hφ q).fderiv, (hasFDerivAt_sliceX hh q).fderiv, map_add]

theorem gradₓ_const_mul (hh : Differentiable ℝ h) (a : ℝ) (q : E d × ℝ) :
    gradₓ (fun q ↦ a * h q) q = a • gradₓ h q := by
  have H : HasFDerivAt (fun y : E d ↦ a * h (y, q.2)) _ q.1 :=
    (hasFDerivAt_sliceX hh q).const_mul a
  simp only [gradₓ, gradient]
  rw [H.fderiv, (hasFDerivAt_sliceX hh q).fderiv]
  simp

theorem gradₓ_add_const (h : E d × ℝ → ℝ) (b : ℝ) (q : E d × ℝ) :
    gradₓ (fun q ↦ h q + b) q = gradₓ h q := by
  simp [gradₓ, gradient]

theorem lapₓ_add (hφ : ContDiff ℝ 2 φ) (hh : ContDiff ℝ 2 h) (q : E d × ℝ) :
    lapₓ (fun q ↦ φ q + h q) q = lapₓ φ q + lapₓ h q :=
  (contDiff_sliceX hφ q.2).contDiffAt.laplacian_add (contDiff_sliceX hh q.2).contDiffAt

theorem lapₓ_const_mul (hh : ContDiff ℝ 2 h) (a : ℝ) (q : E d × ℝ) :
    lapₓ (fun q ↦ a * h q) q = a * lapₓ h q :=
  laplacian_smul a (contDiff_sliceX hh q.2).contDiffAt

theorem lapₓ_add_const (hh : ContDiff ℝ 2 h) (b : ℝ) (q : E d × ℝ) :
    lapₓ (fun q ↦ h q + b) q = lapₓ h q := by
  have := (contDiff_sliceX hh q.2).contDiffAt.laplacian_add
    (contDiffAt_const (c := b) (x := q.1))
  simp only [laplacian_const, Pi.zero_apply, add_zero] at this
  exact this

/-- Heat operator of a perturbation `φ + (a h + b)`. -/
theorem dₜ_sub_lapₓ_add_mul_add (hφ : ContDiff ℝ 2 φ) (hh : ContDiff ℝ 2 h) (a b : ℝ)
    (q : E d × ℝ) :
    dₜ (fun q ↦ φ q + (a * h q + b)) q - lapₓ (fun q ↦ φ q + (a * h q + b)) q =
      (dₜ φ q - lapₓ φ q) + a * (dₜ h q - lapₓ h q) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hhd : Differentiable ℝ h := hh.differentiable two_ne_zero
  have hk : ContDiff ℝ 2 (fun q ↦ a * h q + b) := (contDiff_const.mul hh).add contDiff_const
  rw [dₜ_add hφd (hk.differentiable two_ne_zero), lapₓ_add hφ hk, dₜ_add_const,
    lapₓ_add_const (contDiff_const.mul hh), dₜ_const_mul hhd, lapₓ_const_mul hh]
  ring

/-- Spatial gradient of a perturbation `φ + (a h + b)`. -/
theorem gradₓ_add_mul_add (hφ : Differentiable ℝ φ) (hh : Differentiable ℝ h) (a b : ℝ)
    (q : E d × ℝ) :
    gradₓ (fun q ↦ φ q + (a * h q + b)) q = gradₓ φ q + a • gradₓ h q := by
  have hk : Differentiable ℝ (fun q ↦ a * h q + b) :=
    ((differentiable_const a).mul hh).add (differentiable_const b)
  rw [gradₓ_add hφ hk, gradₓ_add_const, gradₓ_const_mul hh]

end Slices

/-! ### Second-order conditions at a minimum -/

section SecondOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- At a local minimum of a `C²` function `f`, the second derivative in every direction is
nonnegative. -/
theorem iteratedFDeriv_two_nonneg_of_isLocalMin {f : F → ℝ} {x : F} (hf : ContDiff ℝ 2 f)
    (hmin : IsLocalMin f x) (v : F) : 0 ≤ iteratedFDeriv ℝ 2 f x ![v, v] := by
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  set g : ℝ → ℝ := fun s ↦ f (x + s • v) with hg
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ x + s • v) v s := fun s ↦ by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hd1 : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hdg : ∀ s, HasDerivAt g (fderiv ℝ f (x + s • v) v) s := fun s ↦
    (hd1 _).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hderiv : deriv g = fun s ↦ fderiv ℝ f (x + s • v) v := funext fun s ↦ (hdg s).deriv
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hd2 : HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • v) v) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have h1 : HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • v)) (fderiv ℝ (fderiv ℝ f) x v) 0 := by
      have := ((hf'.differentiable one_ne_zero) (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) (hline 0)
      simpa [Function.comp_def] using this
    simpa using h1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hdd : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ f) x v v := by rw [hderiv]; exact hd2.deriv
  by_contra hneg
  rw [not_le] at hneg
  have hgmin : IsLocalMin g 0 := by
    refine IsLocalMin.comp_continuous (by simpa using hmin) ?_
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hg0 : deriv g 0 = 0 := hgmin.deriv_eq_zero
  have hgmax : IsLocalMax g 0 :=
    isLocalMax_of_deriv_deriv_neg (by rw [hdd]; exact hneg) hg0
      (hdg 0).differentiableAt.continuousAt
  -- `g` is locally constant at `0`, so its second derivative vanishes there.
  have hconst : g =ᶠ[𝓝 0] fun _ ↦ g 0 := by
    filter_upwards [hgmin, hgmax] with s h1 h2 using le_antisymm h2 h1
  have hdconst : deriv g =ᶠ[𝓝 0] fun _ ↦ 0 := by
    filter_upwards [hconst.eventuallyEq_nhds] with s hs
    rw [hs.deriv_eq]; simp
  have : deriv (deriv g) 0 = 0 := by rw [hdconst.deriv_eq]; simp
  linarith

/-- At a local minimum of a `C²` function on a finite-dimensional real inner product space, the
Laplacian is nonnegative. -/
theorem laplacian_nonneg_of_isLocalMin {f : F → ℝ} {x : F} (hf : ContDiff ℝ 2 f)
    (hmin : IsLocalMin f x) : 0 ≤ Δ f x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact Finset.sum_nonneg fun i _ ↦ iteratedFDeriv_two_nonneg_of_isLocalMin hf hmin _

end SecondOrder

section SpaceTime

variable {φ : E d × ℝ → ℝ}

/-- If the time slice `y ↦ φ (y, p.2)` has a local minimum at `p.1`, then `Δₓφ(p) ≥ 0`. -/
theorem lapₓ_nonneg_of_isLocalMin (hφ : ContDiff ℝ 2 φ) {p : E d × ℝ}
    (hmin : IsLocalMin (fun y ↦ φ (y, p.2)) p.1) : 0 ≤ lapₓ φ p :=
  laplacian_nonneg_of_isLocalMin (contDiff_sliceX hφ p.2) hmin

/-- If the time slice `y ↦ φ (y, p.2)` has a local minimum at `p.1`, then `∇ₓφ(p) = 0`. -/
theorem gradₓ_eq_zero_of_isLocalMin {p : E d × ℝ}
    (hmin : IsLocalMin (fun y ↦ φ (y, p.2)) p.1) : gradₓ φ p = 0 := by
  simp [gradₓ, gradient, hmin.fderiv_eq_zero]

/-- If `s ↦ φ (p.1, s)` has a minimum at `p.2` among earlier times, then `∂ₜφ(p) ≤ 0`. -/
theorem dₜ_nonpos_of_isLocalMinOn_Iic (hφ : Differentiable ℝ φ) {p : E d × ℝ}
    (hmin : IsLocalMinOn (fun s ↦ φ (p.1, s)) (Iic p.2) p.2) : dₜ φ p ≤ 0 := by
  have hd := hasDerivAt_sliceT hφ p
  have hmem : (-1 : ℝ) ∈ posTangentConeAt (Iic p.2) p.2 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [segment_symm, segment_eq_Icc (by linarith)]
    exact Icc_subset_Iic_self
  have := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hmem
  rw [dₜ_eq_fderiv hφ]
  simpa using this

end SpaceTime

end BernoulliComparison
