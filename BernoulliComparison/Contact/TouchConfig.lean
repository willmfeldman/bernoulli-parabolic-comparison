/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.LocalConstants
public import BernoulliComparison.Touching.ClassBridge

/-!
# Touching data at the contact

Around a point `x⋆ ∈ Ū` put `W⋆ = B_{2λ}(x⋆)` (`Config.Wstar`) and
`O₀ = (W⋆ ∩ U₀) × (0, T]`, `O₁ = (W⋆ ∩ U₁) × (2μ, T]`, `O = (W⋆ ∩ U) × (0, T]`
(`Config.O₀`, `Config.O₁`, `Config.O`). With the constants `c₁ = Config.cSub x⋆`,
`c₂ = Config.cSuper x⋆` of `Contact/LocalConstants.lean`:

(a) `TSub(O₀, E₀, u₀, c₁)`, `TSuper(O₀, v₀, c₂)`, `TSub(O₁, E₁, u₁, c₁)`, `TSuper(O₁, v₁, c₂)`,
`TSub(O, E, û, c₁)`, `TSuper(O, v̂, c₂)`;

(b) `Subcal(U₀ × (0, T], u₀)`, `Subcal(U₁ × (2μ, T], u₁)`, `Subcal(U × (0, T], û)`,
`Supercal({v₀ > 0} ∩ (U₀ × (0, T]), v₀)`, `Supercal({v₁ > 0} ∩ (U₁ × (2μ, T]), v₁)`,
`Supercal({v̂ > 0} ∩ (U × (0, T]), v̂)`.

This is the only place where the Lipschitz `Q` is converted into the constants `c₁ > c₂`: the
gap comes from the factors `1 ± δ` applied to `u` and `v`, together with convolution at spatial
radius `λ`, and it enters only through the touching classes (by monotonicity in `Q`).
A constant `c` is the constant function `fun _ ↦ c`.

The statements hold for every `x⋆ ∈ Ū`; at the contact point `x⋆ ∈ U₁`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Crossing

namespace Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} (P : Config U Q T u v Eset)

/-- `W⋆ = B_{2λ}(x⋆)`. -/
def Wstar (xstar : E d) : Set (E d) := ball xstar (2 * P.lam)

/-- `O = (W⋆ ∩ U) × (0, T]` (the raw level). -/
def O (xstar : E d) : Set (E d × ℝ) := (P.Wstar xstar ∩ U) ×ˢ Ioc 0 T

/-- `O₀ = (W⋆ ∩ U₀) × (0, T]` (level 0). -/
def O₀ (xstar : E d) : Set (E d × ℝ) := (P.Wstar xstar ∩ P.U₀) ×ˢ Ioc 0 T

/-- `O₁ = (W⋆ ∩ U₁) × (2μ, T]` (level 1). -/
def O₁ (xstar : E d) : Set (E d × ℝ) := (P.Wstar xstar ∩ P.U₁) ×ˢ Ioc (2 * P.μ) T

theorem isParOpen_O (xstar : E d) : IsParOpen (P.O xstar) :=
  isParOpen_prod_Ioc (isOpen_ball.inter P.isOpen) _ _

theorem isParOpen_O₀ (xstar : E d) : IsParOpen (P.O₀ xstar) :=
  isParOpen_prod_Ioc (isOpen_ball.inter P.isOpen_U₀) _ _

theorem isParOpen_O₁ (xstar : E d) : IsParOpen (P.O₁ xstar) :=
  isParOpen_prod_Ioc (isOpen_ball.inter P.isOpen_U₁) _ _

theorem O₀_subset (xstar : E d) : P.O₀ xstar ⊆ P.U₀ ×ˢ Ioc 0 T :=
  prod_mono inter_subset_right le_rfl

theorem O₁_subset (xstar : E d) : P.O₁ xstar ⊆ P.U₁ ×ˢ Ioc (2 * P.μ) T :=
  prod_mono inter_subset_right le_rfl

theorem O_subset (xstar : E d) : P.O xstar ⊆ U ×ˢ Ioc 0 T :=
  prod_mono inter_subset_right le_rfl

/-- Points of `W⋆ ∩ U` lie in `Ū ∩ B̄_{2λ}(x⋆)`. -/
theorem mem_closure_dist_le_of_mem_Wstar {xstar x : E d} (hx : x ∈ P.Wstar xstar ∩ U) :
    x ∈ closure U ∧ dist x xstar ≤ 2 * P.lam :=
  ⟨subset_closure hx.2, (mem_ball.mp hx.1).le⟩

theorem ioc_mem_nhdsLE {a b : ℝ} : ∀ t ∈ Ioc a b, Ioc a b ∈ 𝓝[≤] t :=
  fun _ ht ↦ Ioc_mem_nhdsLE_of_mem ht

include P in
theorem continuousOn_Q : ContinuousOn Q U :=
  P.lipschitzOnWith.continuousOn.mono subset_closure

theorem continuousOn_Qsub₀ : ContinuousOn P.Qsub₀ P.U₀ :=
  continuousOn_const.mul ((P.continuousOn_Q.mono P.U₀_subset).sub continuousOn_const)

theorem continuousOn_Qsuper₀ : ContinuousOn P.Qsuper₀ P.U₀ :=
  continuousOn_const.mul ((P.continuousOn_Q.mono P.U₀_subset).add continuousOn_const)

theorem continuousOn_Qsub₁ : ContinuousOn P.Qsub₁ P.U₁ :=
  continuousOn_const.mul ((P.continuousOn_Q.mono P.U₁_subset).sub continuousOn_const)

theorem continuousOn_Qsuper₁ : ContinuousOn P.Qsuper₁ P.U₁ :=
  continuousOn_const.mul ((P.continuousOn_Q.mono P.U₁_subset).add continuousOn_const)

/-! ### (a) touching classes with the constants `c₁`, `c₂` -/

variable {xstar : E d}

/-- Touching configuration (a): `TSub(O₀, E₀, u₀, c₁)`. -/
theorem touchSub_zero (hxs : xstar ∈ closure U) :
    TouchSub (P.O₀ xstar) P.E₀ P.u₀ (fun _ ↦ P.cSub xstar) :=
  ((P.isParaRelaxedSub_zero.touchSub P.isOpen_U₀ ioc_mem_nhdsLE P.continuousOn_Qsub₀).restrict
    (P.O₀_subset xstar)).mono_Q fun p hp ↦ by
      have h := P.mem_closure_dist_le_of_mem_Wstar ⟨hp.1.1, P.U₀_subset hp.1.2⟩
      exact ((P.local_constants hxs).2.2 p.1 h.1 h.2).1.2.1

/-- Touching configuration (a): `TSuper(O₀, v₀, c₂)`. -/
theorem touchSuper_zero (hxs : xstar ∈ closure U) :
    TouchSuper (P.O₀ xstar) P.v₀ (fun _ ↦ P.cSuper xstar) :=
  ((P.isParaSuper_zero.touchSuper P.isOpen_U₀ ioc_mem_nhdsLE P.continuousOn_Qsuper₀).restrict
    (P.O₀_subset xstar) (P.isParOpen_O₀ xstar)).mono_Q fun p hp ↦ by
      have h := P.mem_closure_dist_le_of_mem_Wstar ⟨hp.1.1, P.U₀_subset hp.1.2⟩
      exact ((P.local_constants hxs).2.2 p.1 h.1 h.2).2.2.1

/-- Touching configuration (a): `TSub(O₁, E₁, u₁, c₁)`. -/
theorem touchSub_one (hxs : xstar ∈ closure U) :
    TouchSub (P.O₁ xstar) P.E₁ P.u₁ (fun _ ↦ P.cSub xstar) :=
  ((P.isParaRelaxedSub_one.touchSub P.isOpen_U₁ ioc_mem_nhdsLE P.continuousOn_Qsub₁).restrict
    (P.O₁_subset xstar)).mono_Q fun p hp ↦ by
      have h := P.mem_closure_dist_le_of_mem_Wstar ⟨hp.1.1, P.U₁_subset hp.1.2⟩
      exact ((P.local_constants hxs).2.2 p.1 h.1 h.2).1.2.2

/-- Touching configuration (a): `TSuper(O₁, v₁, c₂)`. -/
theorem touchSuper_one (hxs : xstar ∈ closure U) :
    TouchSuper (P.O₁ xstar) P.v₁ (fun _ ↦ P.cSuper xstar) :=
  ((P.isParaSuper_one.touchSuper P.isOpen_U₁ ioc_mem_nhdsLE P.continuousOn_Qsuper₁).restrict
    (P.O₁_subset xstar) (P.isParOpen_O₁ xstar)).mono_Q fun p hp ↦ by
      have h := P.mem_closure_dist_le_of_mem_Wstar ⟨hp.1.1, P.U₁_subset hp.1.2⟩
      exact ((P.local_constants hxs).2.2 p.1 h.1 h.2).2.2.2

/-- Touching configuration (a): `TSub(O, E, û, c₁)` (raw pair). -/
theorem touchSub_hat (hxs : xstar ∈ closure U) :
    TouchSub (P.O xstar) Eset P.uhat (fun _ ↦ P.cSub xstar) :=
  ((P.isParaRelaxedSub_hat.touchSub P.isOpen ioc_mem_nhdsLE
    (P.continuousOn_Q.const_smul (1 + P.δ))).restrict (P.O_subset xstar)).mono_Q
    fun p hp ↦ by
      have h := P.mem_closure_dist_le_of_mem_Wstar hp.1
      simpa using ((P.local_constants hxs).2.2 p.1 h.1 h.2).1.1

/-- Touching configuration (a): `TSuper(O, v̂, c₂)` (raw supersolution). -/
theorem touchSuper_hat (hxs : xstar ∈ closure U) :
    TouchSuper (P.O xstar) P.vhat (fun _ ↦ P.cSuper xstar) :=
  ((P.isParaSuper_hat.touchSuper P.isOpen ioc_mem_nhdsLE
    (P.continuousOn_Q.const_smul (1 - P.δ))).restrict (P.O_subset xstar)
    (P.isParOpen_O xstar)).mono_Q fun p hp ↦ by
      have h := P.mem_closure_dist_le_of_mem_Wstar hp.1
      simpa using ((P.local_constants hxs).2.2 p.1 h.1 h.2).2.1

/-! ### (b) sub- and supercaloricity -/

/-- Touching configuration (b): `Subcal(U₀ × (0, T], u₀)`. -/
theorem isSubcal_zero : IsSubcal (P.U₀ ×ˢ Ioc 0 T) P.u₀ :=
  P.isParaRelaxedSub_zero.isSubcal P.isOpen_U₀ ioc_mem_nhdsLE

/-- Touching configuration (b): `Subcal(U₁ × (2μ, T], u₁)`. -/
theorem isSubcal_one : IsSubcal (P.U₁ ×ˢ Ioc (2 * P.μ) T) P.u₁ :=
  P.isParaRelaxedSub_one.isSubcal P.isOpen_U₁ ioc_mem_nhdsLE

/-- Touching configuration (b): `Subcal(U × (0, T], û)`. -/
theorem isSubcal_hat : IsSubcal (U ×ˢ Ioc 0 T) P.uhat :=
  P.isParaRelaxedSub_hat.isSubcal P.isOpen ioc_mem_nhdsLE

/-- Touching configuration (b): `Supercal({v₀ > 0} ∩ (U₀ × (0, T]), v₀)`. -/
theorem isSupercal_zero : IsSupercal (posSetP P.v₀ (P.U₀ ×ˢ Ioc 0 T)) P.v₀ :=
  P.isParaSuper_zero.isSupercal_on_pos P.isOpen_U₀ ioc_mem_nhdsLE

/-- Touching configuration (b): `Supercal({v₁ > 0} ∩ (U₁ × (2μ, T]), v₁)`. -/
theorem isSupercal_one : IsSupercal (posSetP P.v₁ (P.U₁ ×ˢ Ioc (2 * P.μ) T)) P.v₁ :=
  P.isParaSuper_one.isSupercal_on_pos P.isOpen_U₁ ioc_mem_nhdsLE

/-- Touching configuration (b): `Supercal({v̂ > 0} ∩ (U × (0, T]), v̂)`. -/
theorem isSupercal_hat : IsSupercal (posSetP P.vhat (U ×ˢ Ioc 0 T)) P.vhat :=
  P.isParaSuper_hat.isSupercal_on_pos P.isOpen ioc_mem_nhdsLE

end Config

end Crossing

namespace Contact

open Crossing

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)}

/-- The touching-class configuration (all items, at levels 0, 1 and raw), for `x⋆ ∈ Ū` with
`c₁ = P.cSub x⋆`, `c₂ = P.cSuper x⋆`. The items are also available separately as
`Config.touchSub_zero`, …, `Config.isSupercal_hat`. -/
theorem touch_config (P : Config U Q T u v Eset) {xstar : E d} (hxs : xstar ∈ closure U) :
    (TouchSub (P.O₀ xstar) P.E₀ P.u₀ (fun _ ↦ P.cSub xstar) ∧
      TouchSuper (P.O₀ xstar) P.v₀ (fun _ ↦ P.cSuper xstar) ∧
      TouchSub (P.O₁ xstar) P.E₁ P.u₁ (fun _ ↦ P.cSub xstar) ∧
      TouchSuper (P.O₁ xstar) P.v₁ (fun _ ↦ P.cSuper xstar) ∧
      TouchSub (P.O xstar) Eset P.uhat (fun _ ↦ P.cSub xstar) ∧
      TouchSuper (P.O xstar) P.vhat (fun _ ↦ P.cSuper xstar)) ∧
    (IsSubcal (P.U₀ ×ˢ Ioc 0 T) P.u₀ ∧ IsSubcal (P.U₁ ×ˢ Ioc (2 * P.μ) T) P.u₁ ∧
      IsSubcal (U ×ˢ Ioc 0 T) P.uhat ∧
      IsSupercal (posSetP P.v₀ (P.U₀ ×ˢ Ioc 0 T)) P.v₀ ∧
      IsSupercal (posSetP P.v₁ (P.U₁ ×ˢ Ioc (2 * P.μ) T)) P.v₁ ∧
      IsSupercal (posSetP P.vhat (U ×ˢ Ioc 0 T)) P.vhat) :=
  ⟨⟨P.touchSub_zero hxs, P.touchSuper_zero hxs, P.touchSub_one hxs, P.touchSuper_one hxs,
      P.touchSub_hat hxs, P.touchSuper_hat hxs⟩,
    ⟨P.isSubcal_zero, P.isSubcal_one, P.isSubcal_hat, P.isSupercal_zero, P.isSupercal_one,
      P.isSupercal_hat⟩⟩

end Contact

end BernoulliComparison
