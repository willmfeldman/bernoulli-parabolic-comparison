/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Contact.Balls

/-!
# The contact data

`Contact.ContactData P` bundles everything that the analysis of the non-polar and polar contact
cases (`NonPolar/`, `Polar/`) uses about a first contact point of the
configuration `P`. It is not a hypothesis structure: it is produced by
`Contact.exists_contactData` from the crossing hypothesis `P.crossingSet.Nonempty` (via
`Config.first_crossing`).

## Data

* `pstar = p⋆ = (x⋆, t⋆)` (`C.xstar`, `C.tstar`), a point of the contact set `Ξ` at the first
  crossing time;
* `q₁`, `q₂`, the interior and exterior touching points on the dual sphere `|q - p̂| = μ`.

Derived (definitions in the namespace `ContactData`): the dual centre `C.phat = p⋆ - μ e_t`,
the unit normals `C.ν₁ = (q₁ - p̂)/μ`, `C.ν₂ = (q₂ - p̂)/μ` (Euclidean unit vectors,
`C.ν₁_unit`; `e_t` is `(0, 1)`), the ball centres `C.ctr₁ = p⋆ + μ ν₁ = q₁ + μ e_t`, `C.ctr₂`
(named `ctr` to avoid a clash with the constants), the constants `C.c₁ > C.c₂ > 0` of
`Contact/LocalConstants.lean` at `x⋆`, `C.Wstar = B_{2λ}(x⋆)`, and `C.O`, `C.O₀`, `C.O₁`.

## Facts

Fields: the first-contact facts (`isFirstContact`), the zero contact values (`u₁_pstar`,
`v₁_pstar`), the contact structure (i)–(iv), and the dual-ball lemma (inclusions, (a)–(f)).
Lemmas in the namespace `ContactData`: the touching-class configuration at levels 0, 1 and raw
(`C.touchSub_zero`, …, `C.isSupercal_hat`), the gap (`C.c₂_pos`, `C.c₂_lt_c₁`), the room, the
location of `q₁`, `q₂`, and the unit normals.

The level-0 objects and the raw pair are the definitions of the configuration:
`P.E₀ = setConv P.D₀ P.K₀ Eset` (`E₀ = D₀ ∩ (E ⊖ K₀)`), `P.u₀ = supConv P.K₀ P.uhat`,
`P.v₀ = infConv P.K₀ P.vhat`, `P.uhat = (1 + δ) u`, `P.vhat = (1 - δ) v`, and `Eset` itself; their
properties are `Config` lemmas (`Config.isParaRelaxedSub_hat`, `Config.mem_Eset_of_uhat_pos`,
`Config.past_points_hat`, `Config.u₁_eq`, `Config.v₁_eq`, `Config.E₁_eq`, …).
-/

@[expose] public section

open Set Filter Topology Metric

namespace BernoulliComparison

namespace Crossing

namespace Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} (P : Config U Q T u v Eset)

include P in
/-- Past points for the raw pair `(û, E)` (for `(1 + δ) Q`), Euclidean form: every
`p ∈ E ∩ (U × (0, T])` is a limit of points of `E` at strictly earlier times. -/
theorem past_points_hat {p : E d × ℝ} (hpE : p ∈ Eset) (hp : p ∈ U ×ˢ Ioc 0 T) {ε : ℝ}
    (hε : 0 < ε) : ∃ q ∈ Eset, q.2 < p.2 ∧ ‖q.1 - p.1‖ ^ 2 + (q.2 - p.2) ^ 2 < ε ^ 2 := by
  have hQ : ContinuousAt ((1 + P.δ) • Q) p.1 :=
    ((P.continuousOn_Q.const_smul (1 + P.δ)).continuousAt (P.isOpen.mem_nhds hp.1) :)
  have hpos : 0 < ((1 + P.δ) • Q) p.1 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos P.one_add_δ_pos (P.c_pos.trans_le (P.c_le _ (subset_closure hp.1)))
  exact P.isParaRelaxedSub_hat.past_points_euclidean P.isOpen hp.1
    (Ioc_mem_nhdsLE_of_mem hp.2) hQ hpos hpE hε

end Config

end Crossing

namespace Contact

open Crossing Config

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)}

/-- The contact data at a first contact point of the configuration `P`. Produced by
`exists_contactData`; see the module docstring for the derived objects and lemmas. -/
structure ContactData (P : Config U Q T u v Eset) where
  /-- The contact point `p⋆ = (x⋆, t⋆) ∈ Ξ`. -/
  pstar : E d × ℝ
  /-- The interior touching point `q₁ ∈ E₀` on the dual sphere. -/
  q₁ : E d × ℝ
  /-- The exterior touching point `q₂ ∈ {v₀ = 0}` on the dual sphere. -/
  q₂ : E d × ℝ
  /-- First crossing: `p⋆ ∈ Ξ ∩ R₁` at the first crossing time `t⋆ = p⋆.2`. -/
  isFirstContact : P.IsFirstContact pstar
  /-- Zero contact value: `u₁(p⋆) = 0`. -/
  u₁_pstar : P.u₁ pstar = 0
  /-- Zero contact value: `v₁(p⋆) = 0`. -/
  v₁_pstar : P.v₁ pstar = 0
  /-- Contact structure (i): `E₁ ∩ {t < t⋆} ⊆ {v₁ > 0}`. -/
  v₁_pos_of_past : ∀ p ∈ P.E₁, p.2 < pstar.2 → 0 < P.v₁ p
  /-- Contact structure (ii): `p⋆ ∈ closure (E₁ ∩ {t < t⋆})`. -/
  mem_closure_past : pstar ∈ closure (P.E₁ ∩ {p | p.2 < pstar.2})
  /-- Contact structure (iii): `p⋆ ∈ closure {p ∈ D₁ | v₁ p > 0, p.2 < t⋆}`. -/
  mem_closure_pos_past : pstar ∈ closure {p ∈ P.D₁ | 0 < P.v₁ p ∧ p.2 < pstar.2}
  /-- Contact structure (iv): `p⋆ ∈ closure ((D₁ \ E₁) ∩ {t < t⋆})`. -/
  mem_closure_exterior_past : pstar ∈ closure ((P.D₁ \ P.E₁) ∩ {p | p.2 < pstar.2})
  /-- Dual-ball lemma: `B̄_μ(p̂) ⊆ B̄_μ(x⋆) × [t⋆ - 2μ, t⋆]`. -/
  dualBall_subset_prod :
    stBall (P.dualCentre pstar) P.μ ⊆ closedBall pstar.1 P.μ ×ˢ Icc (pstar.2 - 2 * P.μ) pstar.2
  /-- Dual-ball lemma: `B̄_μ(x⋆) × [t⋆ - 2μ, t⋆] ⊆ U₀ × (0, T]`. -/
  prod_subset_U₀_Ioc : closedBall pstar.1 P.μ ×ˢ Icc (pstar.2 - 2 * P.μ) pstar.2 ⊆ P.U₀ ×ˢ Ioc 0 T
  /-- `B_μ(p̂) ⊆ (U₁ × (2μ, T]) ∩ {t < t⋆}` (room; used in the reduction to the south pole). -/
  dualBallOpen_subset_past :
    stBallOpen (P.dualCentre pstar) P.μ ⊆ (P.U₁ ×ˢ Ioc (2 * P.μ) T) ∩ {p | p.2 < pstar.2}
  /-- Dual-ball lemma (a): `E₀ ∩ B_μ(p̂) = ∅`. -/
  dual_not_mem_E₀ : ∀ q ∈ stBallOpen (P.dualCentre pstar) P.μ, q ∉ P.E₀
  /-- Dual-ball lemma (a): `u₀ = 0` on `B̄_μ(p̂)`. -/
  dual_u₀_eq_zero : ∀ q ∈ stBall (P.dualCentre pstar) P.μ, P.u₀ q = 0
  /-- Dual-ball lemma (b): `v₀ > 0` on `B_μ(p̂)`. -/
  dual_v₀_pos : ∀ q ∈ stBallOpen (P.dualCentre pstar) P.μ, 0 < P.v₀ q
  /-- Dual-ball lemma (c): `q₁ ∈ E₀`. -/
  q₁_mem_E₀ : q₁ ∈ P.E₀
  /-- Dual-ball lemma (c): `|q₁ - p̂| = μ`. -/
  q₁_sphere : ‖q₁.1 - pstar.1‖ ^ 2 + (q₁.2 - (pstar.2 - P.μ)) ^ 2 = P.μ ^ 2
  /-- Dual-ball lemma (c): `u₀(q₁) = 0`. -/
  u₀_q₁ : P.u₀ q₁ = 0
  /-- Dual-ball lemma (c): `|q₂ - p̂| = μ`. -/
  q₂_sphere : ‖q₂.1 - pstar.1‖ ^ 2 + (q₂.2 - (pstar.2 - P.μ)) ^ 2 = P.μ ^ 2
  /-- Dual-ball lemma (c): `v₀(q₂) = 0`. -/
  v₀_q₂ : P.v₀ q₂ = 0
  /-- Dual-ball lemma (d): `B̄_μ(q₁ + μ e_t) ∩ D₁ ⊆ E₁` (interior ball). -/
  interior_ball : ∀ p ∈ P.D₁, p ∈ stBall (q₁ + (0, P.μ)) P.μ → p ∈ P.E₁
  /-- Dual-ball lemma (d): `B̄_μ(q₂ + μ e_t) ∩ D₁ ⊆ {v₁ = 0}` (exterior ball). -/
  exterior_ball : ∀ p ∈ P.D₁, p ∈ stBall (q₂ + (0, P.μ)) P.μ → P.v₁ p = 0
  /-- Dual-ball lemma (e): `E₁ ∩ B̄_μ(q₂ + μ e_t) ∩ {t < t⋆} = ∅`. -/
  exterior_past : ∀ p ∈ P.E₁, p ∈ stBall (q₂ + (0, P.μ)) P.μ → ¬ p.2 < pstar.2
  /-- Dual-ball lemma (e): `E₁ ∩ B_μ(q₂ + μ e_t) ∩ {t ≤ t⋆} = ∅`. -/
  exterior_open : ∀ p ∈ P.E₁, p ∈ stBallOpen (q₂ + (0, P.μ)) P.μ → ¬ p.2 ≤ pstar.2
  /-- Dual-ball lemma (f): `B̄_μ(q₁ + μ e_t) ∩ D₁ ∩ {t < t⋆} ⊆ {v₁ > 0}`. -/
  interior_past : ∀ p ∈ P.D₁, p ∈ stBall (q₁ + (0, P.μ)) P.μ → p.2 < pstar.2 → 0 < P.v₁ p

/-- Existence of contact data. Under the crossing hypothesis
`S = {p ∈ E₁ | u₁ p ≥ v₁ p} ≠ ∅` there is contact data: a first contact point `p⋆ ∈ Ξ` with the
touching points `q₁`, `q₂` and all the facts recorded in `ContactData`.

The hypothesis `1 ≤ d` (the standing assumption of the contact analysis) is not used by the
proof. -/
theorem exists_contactData (_hd : 1 ≤ d) (P : Config U Q T u v Eset)
    (hS : P.crossingSet.Nonempty) : Nonempty (ContactData P) := by
  obtain ⟨p, h⟩ := P.exists_isFirstContact hS
  obtain ⟨q₁, hq₁E, hq₁s, hq₁u⟩ := exists_q₁ h
  obtain ⟨q₂, hq₂s, hq₂v⟩ := exists_q₂ h
  exact ⟨{
    pstar := p, q₁ := q₁, q₂ := q₂, isFirstContact := h
    u₁_pstar := (zero_contact h).1
    v₁_pstar := (zero_contact h).2
    v₁_pos_of_past := contact_structure_pos h
    mem_closure_past := contact_structure_past h
    mem_closure_pos_past := (contact_structure_pos_past h).2
    mem_closure_exterior_past := contact_structure_exterior_past h
    dualBall_subset_prod := dualBall_subset_prod P p
    prod_subset_U₀_Ioc := prod_subset_U₀_Ioc h
    dualBallOpen_subset_past := dualBallOpen_subset_past h
    dual_not_mem_E₀ := dual_not_mem_E₀ h
    dual_u₀_eq_zero := dual_u₀_eq_zero h
    dual_v₀_pos := dual_v₀_pos h
    q₁_mem_E₀ := hq₁E, q₁_sphere := hq₁s, u₀_q₁ := hq₁u
    q₂_sphere := hq₂s, v₀_q₂ := hq₂v
    interior_ball := interior_ball hq₁E
    exterior_ball := exterior_ball hq₂v
    exterior_past := exterior_past h hq₂v
    exterior_open := exterior_open h hq₂s hq₂v
    interior_past := interior_past h hq₁E }⟩

namespace ContactData

variable {P : Config U Q T u v Eset} (C : ContactData P)

/-! ### Derived objects -/

/-- `x⋆`. -/
def xstar : E d := C.pstar.1

/-- `t⋆`, the first crossing time. -/
def tstar : ℝ := C.pstar.2

/-- The dual centre `p̂ = p⋆ - μ e_t = (x⋆, t⋆ - μ)`. -/
def phat : E d × ℝ := P.dualCentre C.pstar

/-- The interior normal `ν¹ = (q₁ - p̂)/μ` (a Euclidean unit vector, `ν₁_unit`). -/
noncomputable def ν₁ : E d × ℝ := P.μ⁻¹ • (C.q₁ - C.phat)

/-- The exterior normal `ν² = (q₂ - p̂)/μ` (a Euclidean unit vector, `ν₂_unit`). -/
noncomputable def ν₂ : E d × ℝ := P.μ⁻¹ • (C.q₂ - C.phat)

/-- The centre `p⋆ + μ ν¹ = q₁ + μ e_t` of the interior ball. -/
def ctr₁ : E d × ℝ := C.q₁ + (0, P.μ)

/-- The centre `p⋆ + μ ν² = q₂ + μ e_t` of the exterior ball. -/
def ctr₂ : E d × ℝ := C.q₂ + (0, P.μ)

/-- The constant `c₁ = (1 + δ)(Q(x⋆) - 3Lλ)` of `Contact/LocalConstants.lean`. -/
def c₁ : ℝ := P.cSub C.xstar

/-- The constant `c₂ = (1 - δ)(Q(x⋆) + 3Lλ)` of `Contact/LocalConstants.lean`. -/
def c₂ : ℝ := P.cSuper C.xstar

/-- `W⋆ = B_{2λ}(x⋆)`. -/
def Wstar : Set (E d) := P.Wstar C.xstar

/-- `O = (W⋆ ∩ U) × (0, T]`. -/
def O : Set (E d × ℝ) := P.O C.xstar

/-- `O₀ = (W⋆ ∩ U₀) × (0, T]`. -/
def O₀ : Set (E d × ℝ) := P.O₀ C.xstar

/-- `O₁ = (W⋆ ∩ U₁) × (2μ, T]`. -/
def O₁ : Set (E d × ℝ) := P.O₁ C.xstar

theorem pstar_eq : C.pstar = (C.xstar, C.tstar) := rfl

theorem phat_eq : C.phat = (C.xstar, C.tstar - P.μ) := rfl

theorem ctr₁_eq : C.ctr₁ = C.q₁ + (0, P.μ) := rfl

theorem ctr₂_eq : C.ctr₂ = C.q₂ + (0, P.μ) := rfl

/-! ### First crossing -/

theorem mem_E₁ : C.pstar ∈ P.E₁ := C.isFirstContact.mem_E₁

theorem mem_D₁ : C.pstar ∈ P.D₁ := C.isFirstContact.mem_D₁

theorem mem_R₁ : C.pstar ∈ P.R₁ := C.isFirstContact.mem_R₁

/-- `p⋆ ∈ Ξ = contactSet t⋆`. -/
theorem mem_contactSet : C.pstar ∈ P.contactSet C.tstar :=
  ⟨C.mem_E₁, rfl, C.isFirstContact.u₁_eq_v₁⟩

/-- First crossing: `u₁ < v₁` on `E₁ ∩ {t < t⋆}`. -/
theorem lt_of_lt : ∀ p ∈ P.E₁, p.2 < C.tstar → P.u₁ p < P.v₁ p := C.isFirstContact.lt_of_lt

/-- First crossing: `u₁ ≤ v₁` on `E₁ ∩ {t = t⋆}`. -/
theorem le_of_eq : ∀ p ∈ P.E₁, p.2 = C.tstar → P.u₁ p ≤ P.v₁ p := C.isFirstContact.le_of_eq

theorem xstar_mem_U₁ : C.xstar ∈ P.U₁ := C.isFirstContact.fst_mem_U₁

theorem xstar_mem_U : C.xstar ∈ U := C.isFirstContact.fst_mem_U

theorem xstar_mem_closure : C.xstar ∈ closure U := C.isFirstContact.fst_mem_closure

/-- `B̄_λ(x⋆) ⊆ U`. -/
theorem closedBall_lam_subset : closedBall C.xstar P.lam ⊆ U := C.xstar_mem_U₁

theorem ρ₀_le_tstar : P.ρ₀ ≤ C.tstar := C.isFirstContact.ρ₀_le

theorem tstar_le_T : C.tstar ≤ T := C.isFirstContact.le_T

theorem two_μ_lt_tstar : 2 * P.μ < C.tstar := C.isFirstContact.two_μ_lt

/-- `8λ < t⋆` (from (P1) and `ρ₀ ≤ t⋆`). -/
theorem eight_lam_lt_tstar : 8 * P.lam < C.tstar := by
  have := P.lam_lt; have := C.ρ₀_le_tstar; linarith

/-- The room at `p⋆` (from the margin of the convolved pair):
`B̄_{2r₀}(x⋆) × [t⋆ - 2r₀, t⋆] ⊆ U₁ × (2μ, T]` and `2λ < r₀`. -/
theorem room : closedBall C.xstar (2 * P.r₀) ×ˢ Icc (C.tstar - 2 * P.r₀) C.tstar ⊆
    P.U₁ ×ˢ Ioc (2 * P.μ) T ∧ 2 * P.lam < P.r₀ :=
  C.isFirstContact.room

/-- The room in pointwise form. -/
theorem mem_room {q : E d × ℝ} (hx : ‖q.1 - C.xstar‖ ≤ 2 * P.r₀)
    (ht1 : C.tstar - 2 * P.r₀ ≤ q.2) (ht2 : q.2 ≤ C.tstar) : q ∈ P.U₁ ×ˢ Ioc (2 * P.μ) T :=
  C.isFirstContact.mem_room hx ht1 ht2

/-! ### Normals and centres -/

theorem q₁_mem_stBall : C.q₁ ∈ stBall C.phat P.μ := mem_stBall_of_sphere C.q₁_sphere

theorem q₂_mem_stBall : C.q₂ ∈ stBall C.phat P.μ := mem_stBall_of_sphere C.q₂_sphere

theorem q₁_not_mem_stBallOpen : C.q₁ ∉ stBallOpen C.phat P.μ := fun h ↦
  C.dual_not_mem_E₀ _ h C.q₁_mem_E₀

theorem q₂_not_mem_stBallOpen : C.q₂ ∉ stBallOpen C.phat P.μ := fun h ↦
  (C.dual_v₀_pos _ h).ne' C.v₀_q₂

theorem ν_unit_aux {q : E d × ℝ}
    (hq : ‖q.1 - C.pstar.1‖ ^ 2 + (q.2 - (C.pstar.2 - P.μ)) ^ 2 = P.μ ^ 2) :
    ‖(P.μ⁻¹ • (q - C.phat)).1‖ ^ 2 + (P.μ⁻¹ • (q - C.phat)).2 ^ 2 = 1 := by
  have hμ := P.μ_pos
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hμ, smul_eq_mul, phat, dualCentre]
  rw [mul_pow, mul_pow, ← mul_add, hq, inv_pow, inv_mul_cancel₀ (by positivity)]

/-- `ν¹` is a Euclidean unit vector: `‖ν¹ₓ‖² + (ν¹ₜ)² = 1`. -/
theorem ν₁_unit : ‖C.ν₁.1‖ ^ 2 + C.ν₁.2 ^ 2 = 1 := C.ν_unit_aux C.q₁_sphere

/-- `ν²` is a Euclidean unit vector: `‖ν²ₓ‖² + (ν²ₜ)² = 1`. -/
theorem ν₂_unit : ‖C.ν₂.1‖ ^ 2 + C.ν₂.2 ^ 2 = 1 := C.ν_unit_aux C.q₂_sphere

theorem q₁_eq : C.q₁ = C.phat + P.μ • C.ν₁ := by
  rw [ν₁, smul_smul, mul_inv_cancel₀ P.μ_pos.ne', one_smul, add_sub_cancel]

theorem q₂_eq : C.q₂ = C.phat + P.μ • C.ν₂ := by
  rw [ν₂, smul_smul, mul_inv_cancel₀ P.μ_pos.ne', one_smul, add_sub_cancel]

theorem pstar_sub_phat : C.pstar - C.phat = ((0 : E d), P.μ) := by
  ext <;> simp [phat, dualCentre]

/-- `c₁ = p⋆ + μ ν¹` (the interior centre as a point on the normal). -/
theorem ctr₁_eq_pstar_add : C.ctr₁ = C.pstar + P.μ • C.ν₁ := by
  rw [ctr₁, C.q₁_eq, ← C.pstar_sub_phat]; abel

/-- `c₂ = p⋆ + μ ν²` (the exterior centre as a point on the normal). -/
theorem ctr₂_eq_pstar_add : C.ctr₂ = C.pstar + P.μ • C.ν₂ := by
  rw [ctr₂, C.q₂_eq, ← C.pstar_sub_phat]; abel

/-- `ν¹ = e_t` iff `q₁ = p⋆` (north pole). -/
theorem ν₁_eq_et_iff : C.ν₁ = ((0 : E d), (1 : ℝ)) ↔ C.q₁ = C.pstar := by
  have hμ := P.μ_pos.ne'
  rw [C.q₁_eq]
  constructor
  · intro h; rw [h]; ext <;> simp [phat, dualCentre]
  · intro h
    have h2 : P.μ • C.ν₁ = P.μ • ((0 : E d), (1 : ℝ)) := by
      rw [eq_sub_of_add_eq' h, C.pstar_sub_phat]; ext <;> simp
    exact smul_right_injective _ hμ h2

/-- `ν² = e_t` iff `q₂ = p⋆` (north pole). -/
theorem ν₂_eq_et_iff : C.ν₂ = ((0 : E d), (1 : ℝ)) ↔ C.q₂ = C.pstar := by
  have hμ := P.μ_pos.ne'
  rw [C.q₂_eq]
  constructor
  · intro h; rw [h]; ext <;> simp [phat, dualCentre]
  · intro h
    have h2 : P.μ • C.ν₂ = P.μ • ((0 : E d), (1 : ℝ)) := by
      rw [eq_sub_of_add_eq' h, C.pstar_sub_phat]; ext <;> simp
    exact smul_right_injective _ hμ h2

/-! ### Location of the touching points -/

theorem q₁_mem_prod : C.q₁ ∈ closedBall C.xstar P.μ ×ˢ Icc (C.tstar - 2 * P.μ) C.tstar :=
  sphere_mem_prod C.q₁_sphere

theorem q₂_mem_prod : C.q₂ ∈ closedBall C.xstar P.μ ×ˢ Icc (C.tstar - 2 * P.μ) C.tstar :=
  sphere_mem_prod C.q₂_sphere

/-- `|q₁ - p⋆| ≤ 2μ`. -/
theorem stNorm_q₁_sub_le : stNorm (C.q₁ - C.pstar) ≤ 2 * P.μ :=
  stNorm_sub_le_of_sphere C.q₁_sphere

/-- `|q₂ - p⋆| ≤ 2μ`. -/
theorem stNorm_q₂_sub_le : stNorm (C.q₂ - C.pstar) ≤ 2 * P.μ :=
  stNorm_sub_le_of_sphere C.q₂_sphere

theorem q₁_mem_O₀ : C.q₁ ∈ C.O₀ := sphere_mem_O₀ C.isFirstContact C.q₁_sphere

theorem q₂_mem_O₀ : C.q₂ ∈ C.O₀ := sphere_mem_O₀ C.isFirstContact C.q₂_sphere

theorem q₁_mem_O : C.q₁ ∈ C.O := sphere_mem_O C.isFirstContact C.q₁_sphere

theorem q₂_mem_O : C.q₂ ∈ C.O := sphere_mem_O C.isFirstContact C.q₂_sphere

theorem q₁_mem_D₀ : C.q₁ ∈ P.D₀ := P.E₀_subset_D₀ C.q₁_mem_E₀

theorem q₂_mem_D₀ : C.q₂ ∈ P.D₀ :=
  P.prod_Ioc_subset_D₀ (C.prod_subset_U₀_Ioc C.q₂_mem_prod)

/-! ### Local constants and touching data -/

theorem c₂_pos : 0 < C.c₂ := P.cSuper_pos C.xstar_mem_closure

/-- The gap `c₂ < c₁` coming from the factors `1 ± δ`. -/
theorem c₂_lt_c₁ : C.c₂ < C.c₁ := P.cSuper_lt_cSub C.xstar_mem_closure

theorem c₁_pos : 0 < C.c₁ := P.cSub_pos C.xstar_mem_closure

theorem isParOpen_O : IsParOpen C.O := P.isParOpen_O _

theorem isParOpen_O₀ : IsParOpen C.O₀ := P.isParOpen_O₀ _

theorem isParOpen_O₁ : IsParOpen C.O₁ := P.isParOpen_O₁ _

/-- Touching configuration (a): `TSub(O₀, E₀, u₀, c₁)`. -/
theorem touchSub_zero : TouchSub C.O₀ P.E₀ P.u₀ (fun _ ↦ C.c₁) :=
  P.touchSub_zero C.xstar_mem_closure

/-- Touching configuration (a): `TSuper(O₀, v₀, c₂)`. -/
theorem touchSuper_zero : TouchSuper C.O₀ P.v₀ (fun _ ↦ C.c₂) :=
  P.touchSuper_zero C.xstar_mem_closure

/-- Touching configuration (a): `TSub(O₁, E₁, u₁, c₁)`. -/
theorem touchSub_one : TouchSub C.O₁ P.E₁ P.u₁ (fun _ ↦ C.c₁) :=
  P.touchSub_one C.xstar_mem_closure

/-- Touching configuration (a): `TSuper(O₁, v₁, c₂)`. -/
theorem touchSuper_one : TouchSuper C.O₁ P.v₁ (fun _ ↦ C.c₂) :=
  P.touchSuper_one C.xstar_mem_closure

/-- Touching configuration (a): `TSub(O, E, û, c₁)` (raw pair). -/
theorem touchSub_hat : TouchSub C.O Eset P.uhat (fun _ ↦ C.c₁) :=
  P.touchSub_hat C.xstar_mem_closure

/-- Touching configuration (a): `TSuper(O, v̂, c₂)` (raw). -/
theorem touchSuper_hat : TouchSuper C.O P.vhat (fun _ ↦ C.c₂) :=
  P.touchSuper_hat C.xstar_mem_closure

/-- Touching configuration (b): `Subcal(U₀ × (0, T], u₀)`. -/
theorem isSubcal_zero : IsSubcal (P.U₀ ×ˢ Ioc 0 T) P.u₀ := P.isSubcal_zero

/-- Touching configuration (b): `Subcal(U₁ × (2μ, T], u₁)`. -/
theorem isSubcal_one : IsSubcal (P.U₁ ×ˢ Ioc (2 * P.μ) T) P.u₁ := P.isSubcal_one

/-- Touching configuration (b): `Subcal(U × (0, T], û)`. -/
theorem isSubcal_hat : IsSubcal (U ×ˢ Ioc 0 T) P.uhat := P.isSubcal_hat

/-- Touching configuration (b): `Supercal({v₀ > 0} ∩ (U₀ × (0, T]), v₀)`. -/
theorem isSupercal_zero : IsSupercal (posSetP P.v₀ (P.U₀ ×ˢ Ioc 0 T)) P.v₀ := P.isSupercal_zero

/-- Touching configuration (b): `Supercal({v₁ > 0} ∩ (U₁ × (2μ, T]), v₁)`. -/
theorem isSupercal_one : IsSupercal (posSetP P.v₁ (P.U₁ ×ˢ Ioc (2 * P.μ) T)) P.v₁ :=
  P.isSupercal_one

/-- Touching configuration (b): `Supercal({v̂ > 0} ∩ (U × (0, T]), v̂)`. -/
theorem isSupercal_hat : IsSupercal (posSetP P.vhat (U ×ˢ Ioc 0 T)) P.vhat := P.isSupercal_hat

end ContactData

end Contact

end BernoulliComparison
