/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barrier.Margin
public import BernoulliComparison.Convolution.Kernel
public import BernoulliComparison.Convolution.Preservation
public import BernoulliComparison.Convolution.Compose

/-!
# Parameters and the convolved configuration

The parameters and the twice-convolved configuration used in the proof of the main comparison
theorem (`para_relaxed_comparison`).

* `Crossing.Params U Q T u v E` bundles the hypotheses of the main theorem (after the margin
  `u + θ ≤ v` has been extracted from the neighbourhood `N` by `margin_of_nhdsSet`), the
  δ-scaling constants of `exists_delta_scaling`, and the convolution radii `λ₁ > 0`, `μ > 0`
  with (P1)–(P3). In Lean `λ₁` is written `ℓ` (`λ` is a keyword) and `λ = λ₁ + μ` is `lam`.
  `Params.nonempty` proves that parameters exist under the hypotheses of the main theorem
  (with `λ₁ = μ`).
* `Crossing.Config := Params`: the configuration is the parameter bundle, and all its objects
  (`U₀, U₁, D₀, D₁, u₀, v₀, E₀, u₁, v₁, E₁, R₁, r₀`, the kernels `K₀, B, K` and the
  scaled pair `û, v̂`) are definitions in the namespace `Config`; nothing about them is
  assumed.
* Properties (a)–(e) of the configuration: (a) convolution steps, (b) the convolved pairs are
  relaxed sub/supersolutions, (c) composition, (d) ordering, (e) continuity etc.:
  `Config.convStep_zero`, `Config.convStep_one`, `Config.convStep_zero_one`;
  `Config.isParaRelaxedSub_zero`, `isParaSuper_zero`, `isParaRelaxedSub_one`, `isParaSuper_one`
  (and `isParaRelaxedSub_hat`, `isParaSuper_hat` for the raw pair); `Config.u₁_eq`,
  `Config.v₁_eq`, `Config.E₁_eq`; `Config.uhat_le_u₁`, `v₁_le_vhat`, `inter_subset_E₁`,
  `interiorRegion_subset_D₁`; continuity/nonnegativity/closedness lemmas.

No hypothesis `D_{ρ₀} ≠ ∅` is needed for any statement proved here (`2μ < T` follows from (P1)
and `ρ₀ ≤ T`); `U₁ ≠ ∅` is not recorded.
-/

@[expose] public section

open Set Filter Topology Metric Pointwise

namespace BernoulliComparison

namespace Crossing

variable {d : ℕ}

/-! ### Auxiliary geometric lemmas -/

/-- `{x | B̄_r(x) ⊆ U}` is open for `U` open (`E d` is proper). -/
theorem isOpen_setOf_closedBall_subset {U : Set (E d)} (hU : IsOpen U) (r : ℝ) :
    IsOpen {x : E d | closedBall x r ⊆ U} := by
  rcases lt_or_ge r 0 with hr | hr
  · simp [closedBall_eq_empty.mpr hr]
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨ε, hε, hth⟩ := (isCompact_closedBall x r).exists_thickening_subset_open hU hx
  rw [thickening_closedBall hε hr] at hth
  refine ⟨ε, hε, fun y hy ↦ ?_⟩
  refine (closedBall_subset_ball' ?_).trans hth
  rw [mem_ball] at hy
  linarith

/-- `{x | B̄_r(x) ⊆ U}` lies in `U` for `r ≥ 0`. -/
theorem setOf_closedBall_subset_subset {U : Set (E d)} {r : ℝ} (hr : 0 ≤ r) :
    {x : E d | closedBall x r ⊆ U} ⊆ U :=
  fun _ hx ↦ hx (mem_closedBall_self hr)

/-- Translation maps closures into closures: if `A + v ⊆ B` then `closure A + v ⊆ closure B`. -/
theorem add_mem_closure_of_forall {A B : Set (E d)} {v x : E d} (h : ∀ y ∈ A, y + v ∈ B)
    (hx : x ∈ closure A) : x + v ∈ closure B :=
  map_mem_closure (f := fun y ↦ y + v) (by fun_prop) hx h

/-- `c • Q` is `(c L)`-Lipschitz if `Q` is `L`-Lipschitz, `c ≥ 0`. -/
theorem lipschitzOnWith_const_smul {s : Set (E d)} {Q : E d → ℝ} {L : NNReal}
    (hQ : LipschitzOnWith L Q s) {c : ℝ} (hc : 0 ≤ c) :
    LipschitzOnWith (.mk c hc * L) (c • Q) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have h := hQ.dist_le_mul x hx y hy
  simp only [Pi.smul_apply, smul_eq_mul, Real.dist_eq, NNReal.coe_mul, NNReal.coe_mk] at h ⊢
  rw [← mul_sub, abs_mul, abs_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left h hc

/-! ### Parameters -/

/-- Parameters for the main comparison argument, together with its standing hypotheses, the
margin and the δ-scaling. The data are: a Lipschitz constant `L` and a lower bound `c > 0` of `Q` on
`Ū`; the margin `0 < ρ₀ ≤ T`, `θ > 0` (`u + θ ≤ v` on `E \ D_{ρ₀}`); a bound `M` of `u + v` on
`D = Ū × [0, T]` and `δ` as in `exists_delta_scaling`; and the convolution radii `λ₁ = ℓ > 0`
and `μ > 0`, `λ = ℓ + μ`, with
(P1) `λ < ρ₀ / 8`, (P2) `8 L λ ≤ δ c`, (P3) `|v̂ q - v̂ q'| ≤ θ'/2 = θ/4` for `q, q' ∈ D` with
`|q - q'| ≤ 3λ` (Euclidean space-time distance), where `v̂ = (1 - δ) v`.

The hypotheses of the main theorem are recorded as fields, so that every lemma about the
configuration takes a single argument `P`. Parameters exist: `Params.nonempty`. -/
structure Params (U : Set (E d)) (Q : E d → ℝ) (T : ℝ) (u v : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) where
  /-- A Lipschitz constant of `Q` on `Ū`. -/
  L : NNReal
  /-- A positive lower bound of `Q` on `Ū`. -/
  c : ℝ
  /-- The margin width. -/
  ρ₀ : ℝ
  /-- The margin `θ > 0`. -/
  θ : ℝ
  /-- A bound of `u + v` on `D`. -/
  M : ℝ
  /-- The scaling parameter `δ`. -/
  δ : ℝ
  /-- The spatial radius `λ₁` of the first convolution step. -/
  ℓ : ℝ
  /-- The radius `μ` of the backward ball `B⁻_μ`. -/
  μ : ℝ
  isOpen : IsOpen U
  isBounded : Bornology.IsBounded U
  lipschitzOnWith : LipschitzOnWith L Q (closure U)
  c_pos : 0 < c
  c_le : ∀ x ∈ closure U, c ≤ Q x
  T_pos : 0 < T
  continuousOn_u : ContinuousOn u (closure U ×ˢ Icc 0 T)
  continuousOn_v : ContinuousOn v (closure U ×ˢ Icc 0 T)
  sub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset
  super : IsParaSuper U Q (Ioc 0 T) v
  ρ₀_pos : 0 < ρ₀
  ρ₀_le : ρ₀ ≤ T
  θ_pos : 0 < θ
  /-- The margin: `u + θ ≤ v` on `E \ D_{ρ₀}`. -/
  margin_uv : ∀ p ∈ Eset, p ∉ interiorRegion U T ρ₀ → u p + θ ≤ v p
  add_le_M : ∀ p ∈ closure U ×ˢ Icc 0 T, u p + v p ≤ M
  δ_pos : 0 < δ
  δ_le_half : δ ≤ 1 / 2
  δ_mul_le : δ * (M + 1) ≤ θ / 2
  ℓ_pos : 0 < ℓ
  μ_pos : 0 < μ
  /-- (P1) `λ < ρ₀ / 8`. -/
  P1 : ℓ + μ < ρ₀ / 8
  /-- (P2) `8 L λ ≤ δ c`. -/
  P2 : 8 * (L : ℝ) * (ℓ + μ) ≤ δ * c
  /-- (P3) the modulus of continuity of `v̂ = (1 - δ) v` on `D` at scale `3λ` is `≤ θ'/2`. -/
  P3 : ∀ q ∈ closure U ×ˢ Icc 0 T, ∀ q' ∈ closure U ×ˢ Icc 0 T,
    ‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2 ≤ (3 * (ℓ + μ)) ^ 2 →
      |(1 - δ) * v q - (1 - δ) * v q'| ≤ θ / 4

/-- A uniform modulus for a function continuous on a compact set, at the Euclidean space-time
scale: there is `η > 0` such that `|w q - w q'| ≤ ε` for `q, q' ∈ S` with
`‖q.1 - q'.1‖² + (q.2 - q'.2)² ≤ η²`. -/
theorem exists_modulus_euclidean {S : Set (E d × ℝ)} {w : E d × ℝ → ℝ} (hS : IsCompact S)
    (hw : ContinuousOn w S) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ q ∈ S, ∀ q' ∈ S, ‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2 ≤ η ^ 2 →
      |w q - w q'| ≤ ε := by
  obtain ⟨η, hη, h⟩ :=
    Metric.uniformContinuousOn_iff_le.mp (hS.uniformContinuousOn_of_continuous hw) ε hε
  refine ⟨η, hη, fun q hq q' hq' hqq' ↦ ?_⟩
  rw [← Real.dist_eq]
  refine h q hq q' hq' ?_
  rw [Prod.dist_eq, dist_eq_norm, Real.dist_eq, max_le_iff]
  constructor
  · have h1 : ‖q.1 - q'.1‖ ^ 2 ≤ η ^ 2 := by nlinarith [sq_nonneg (q.2 - q'.2)]
    exact (sq_le_sq₀ (norm_nonneg _) hη.le).mp h1
  · have h1 : (q.2 - q'.2) ^ 2 ≤ η ^ 2 := by nlinarith [sq_nonneg ‖q.1 - q'.1‖]
    exact abs_le_of_sq_le_sq' h1 hη.le |>.elim (fun a b ↦ abs_le.mpr ⟨a, b⟩)

/-- Parameters exist. Under the hypotheses of the main theorem (the order
`u ≺_E v` on a neighbourhood `N` of `∂ₚ`), there are parameters: the margin comes from
`margin_of_nhdsSet`, `δ` from `exists_delta_scaling`, and `λ₁ = μ = m` with `m > 0` small. -/
theorem Params.nonempty {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
    {Eset N : Set (E d × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    Nonempty (Params U Q T u v Eset) := by
  obtain ⟨L, hL⟩ := hQ
  obtain ⟨c, hc, hcQ⟩ := hQpos
  have hED : Eset ⊆ closure U ×ˢ Icc 0 T := by
    have := hsub.2.2.2.1
    rwa [closure_Ioc hT.ne] at this
  obtain ⟨ρ₀, hρ₀, hρ₀T, θ, hθ, hmargin⟩ :=
    margin_of_nhdsSet hU hUb hT hu hv hsub.2.2.1 hED hN hprec
  obtain ⟨M₀, hM₀⟩ := exists_bound_add_closedDomain hUb hu hv
  obtain ⟨δ, hδ, hδ2, hδθ⟩ := exists_delta_scaling hθ (le_max_right M₀ 0)
  have hD : IsCompact (closure U ×ˢ Icc 0 T) := hUb.isCompact_closure.prod isCompact_Icc
  obtain ⟨η, hη, hmod⟩ := exists_modulus_euclidean hD
    (continuousOn_const.mul hv : ContinuousOn (fun q ↦ (1 - δ) * v q) _)
    (by positivity : 0 < θ / 4)
  set m := min (min (ρ₀ / 32) (δ * c / (16 * ((L : ℝ) + 1)))) (η / 6) with hm
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hm0 : 0 < m := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hm1 : m ≤ ρ₀ / 32 := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : m ≤ δ * c / (16 * ((L : ℝ) + 1)) := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : m ≤ η / 6 := min_le_right _ _
  have hm2' : m * (16 * ((L : ℝ) + 1)) ≤ δ * c := (le_div_iff₀ (by positivity)).mp hm2
  exact ⟨{
    L := L, c := c, ρ₀ := ρ₀, θ := θ, M := max M₀ 0, δ := δ, ℓ := m, μ := m
    isOpen := hU, isBounded := hUb, lipschitzOnWith := hL, c_pos := hc, c_le := hcQ,
    T_pos := hT, continuousOn_u := hu, continuousOn_v := hv, sub := hsub, super := hsuper,
    ρ₀_pos := hρ₀, ρ₀_le := hρ₀T, θ_pos := hθ, margin_uv := hmargin,
    add_le_M := fun p hp ↦ (hM₀ p hp).trans (le_max_left _ _),
    δ_pos := hδ, δ_le_half := hδ2, δ_mul_le := hδθ, ℓ_pos := hm0, μ_pos := hm0,
    P1 := by linarith
    P2 := by nlinarith
    P3 := fun q hq q' hq' hqq' ↦ hmod q hq q' hq' (hqq'.trans (by nlinarith)) }⟩

/-! ### The configuration -/

/-- The convolved configuration. It is determined by the parameters: every object of the
configuration is a definition in the namespace `Config` (no hypothesis structure). -/
abbrev Config (U : Set (E d)) (Q : E d → ℝ) (T : ℝ) (u v : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Type :=
  Params U Q T u v Eset

namespace Config

variable {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)}
  (P : Config U Q T u v Eset)

/-- `λ = λ₁ + μ`. -/
def lam : ℝ := P.ℓ + P.μ

/-- `θ' = θ / 2`. -/
noncomputable def θ' : ℝ := P.θ / 2

/-- The closed domain `D = Ū × [0, T]`. -/
@[nolint unusedArguments]
def D (_P : Config U Q T u v Eset) : Set (E d × ℝ) := closure U ×ˢ Icc 0 T

/-- `û = (1 + δ) u`. -/
def uhat : E d × ℝ → ℝ := (1 + P.δ) • u

/-- `v̂ = (1 - δ) v`. -/
def vhat : E d × ℝ → ℝ := (1 - P.δ) • v

/-- The first (spatial) kernel `K₀ = D̄_{λ₁}`. -/
def K₀ : Set (E d × ℝ) := spDisk 0 P.ℓ

/-- The backward ball `B = B⁻_μ`. -/
def B : Set (E d × ℝ) := backBall P.μ

/-- The kernel `K = K₀ ⊕ B`. -/
def K : Set (E d × ℝ) := diskBallKernel P.ℓ P.μ

/-- `U₀ = {x | B̄_{λ₁}(x) ⊆ U}`. -/
def U₀ : Set (E d) := {x | closedBall x P.ℓ ⊆ U}

/-- `U₁ = {x | B̄_λ(x) ⊆ U}`. -/
def U₁ : Set (E d) := {x | closedBall x P.lam ⊆ U}

/-- `D₀ = Ū₀ × [0, T]`. -/
def D₀ : Set (E d × ℝ) := closure P.U₀ ×ˢ Icc 0 T

/-- `D₁ = Ū₁ × [2μ, T]`. -/
def D₁ : Set (E d × ℝ) := closure P.U₁ ×ˢ Icc (2 * P.μ) T

/-- `u₀ = û^{K₀}`. -/
noncomputable def u₀ : E d × ℝ → ℝ := supConv P.K₀ P.uhat

/-- `v₀ = v̂_{K₀}`. -/
noncomputable def v₀ : E d × ℝ → ℝ := infConv P.K₀ P.vhat

/-- `E₀ = D₀ ∩ (E ⊖ K₀)`. -/
def E₀ : Set (E d × ℝ) := setConv P.D₀ P.K₀ Eset

/-- `u₁ = û^K`. -/
noncomputable def u₁ : E d × ℝ → ℝ := supConv P.K P.uhat

/-- `v₁ = v̂_K`. -/
noncomputable def v₁ : E d × ℝ → ℝ := infConv P.K P.vhat

/-- `E₁ = D₁ ∩ (E ⊖ K)`. -/
def E₁ : Set (E d × ℝ) := setConv P.D₁ P.K Eset

/-- The room region `R₁ = {(x, t) | B̄_{ρ₀ - λ}(x) ⊆ U, ρ₀ ≤ t ≤ T}`. -/
def R₁ : Set (E d × ℝ) := {p | closedBall p.1 (P.ρ₀ - P.lam) ⊆ U ∧ P.ρ₀ ≤ p.2 ∧ p.2 ≤ T}

/-- `r₀ = ρ₀ / 4`. -/
noncomputable def r₀ : ℝ := P.ρ₀ / 4

/-- `Q₀⁻ = (1 + δ)(Q - L λ₁)`. -/
def Qsub₀ : E d → ℝ := fun x ↦ (1 + P.δ) * (Q x - P.L * P.ℓ)

/-- `Q₀⁺ = (1 - δ)(Q + L λ₁)`. -/
def Qsuper₀ : E d → ℝ := fun x ↦ (1 - P.δ) * (Q x + P.L * P.ℓ)

/-- `Q₁⁻ = (1 + δ)(Q - L λ)`. -/
def Qsub₁ : E d → ℝ := fun x ↦ (1 + P.δ) * (Q x - P.L * P.lam)

/-- `Q₁⁺ = (1 - δ)(Q + L λ)`. -/
def Qsuper₁ : E d → ℝ := fun x ↦ (1 - P.δ) * (Q x + P.L * P.lam)

/-! ### Elementary facts about the parameters -/

theorem lam_pos : 0 < P.lam := add_pos P.ℓ_pos P.μ_pos

theorem lam_lt : P.lam < P.ρ₀ / 8 := P.P1

theorem μ_lt_lam : P.μ < P.lam := lt_add_of_pos_left _ P.ℓ_pos

theorem ℓ_lt_lam : P.ℓ < P.lam := lt_add_of_pos_right _ P.μ_pos

theorem two_μ_lt_ρ₀ : 2 * P.μ < P.ρ₀ := by
  have := P.lam_lt; have := P.μ_lt_lam; have := P.ρ₀_pos; linarith

/-- `2μ < T`, from (P1) and `ρ₀ ≤ T`. -/
theorem two_μ_lt_T : 2 * P.μ < T := P.two_μ_lt_ρ₀.trans_le P.ρ₀_le

theorem r₀_pos : 0 < P.r₀ := by unfold r₀; linarith [P.ρ₀_pos]

theorem θ'_pos : 0 < P.θ' := by unfold θ'; linarith [P.θ_pos]

theorem isCompact_D : IsCompact P.D := P.isBounded.isCompact_closure.prod isCompact_Icc

theorem Eset_subset_D : Eset ⊆ P.D := by
  have := P.sub.2.2.2.1
  rwa [closure_Ioc P.T_pos.ne] at this

include P in
theorem isClosed_Eset : IsClosed Eset := P.sub.2.2.1

/-! ### The scaled pair `(û, E)`, `v̂` -/

theorem uhat_apply (p : E d × ℝ) : P.uhat p = (1 + P.δ) * u p := rfl

theorem vhat_apply (p : E d × ℝ) : P.vhat p = (1 - P.δ) * v p := rfl

theorem continuousOn_uhat : ContinuousOn P.uhat P.D := by
  unfold uhat D; exact P.continuousOn_u.const_smul (1 + P.δ)

theorem continuousOn_vhat : ContinuousOn P.vhat P.D := by
  unfold vhat D; exact P.continuousOn_v.const_smul (1 - P.δ)

theorem u_nonneg : ∀ p ∈ P.D, 0 ≤ u p :=
  nonneg_on_closedDomain P.T_pos P.continuousOn_u P.sub.2.1

theorem v_nonneg : ∀ p ∈ P.D, 0 ≤ v p :=
  nonneg_on_closedDomain P.T_pos P.continuousOn_v P.super.2.1

theorem uhat_nonneg {p : E d × ℝ} (hp : p ∈ P.D) : 0 ≤ P.uhat p :=
  mul_nonneg (by linarith [P.δ_pos]) (P.u_nonneg p hp)

theorem vhat_nonneg {p : E d × ℝ} (hp : p ∈ P.D) : 0 ≤ P.vhat p :=
  mul_nonneg (by linarith [P.δ_le_half]) (P.v_nonneg p hp)

/-- The conclusions of `margin_delta_scaled` for the parameters. -/
theorem delta_scaled :
    (∀ p ∈ Eset, p ∉ interiorRegion U T P.ρ₀ → P.uhat p + P.θ / 2 ≤ P.vhat p) ∧
    (∀ p ∈ P.D, u p ≤ P.uhat p ∧ P.vhat p ≤ v p) ∧
    IsParaRelaxedSub U ((1 + P.δ) • Q) (Ioc 0 T) P.uhat Eset ∧
    IsParaSuper U ((1 - P.δ) • Q) (Ioc 0 T) P.vhat :=
  margin_delta_scaled P.sub P.super P.Eset_subset_D P.margin_uv P.u_nonneg P.v_nonneg P.add_le_M
    P.δ_pos P.δ_le_half P.δ_mul_le

/-- The scaled margin: `û + θ' ≤ v̂` on `E \ D_{ρ₀}`. -/
theorem margin_hat : ∀ p ∈ Eset, p ∉ interiorRegion U T P.ρ₀ → P.uhat p + P.θ' ≤ P.vhat p :=
  P.delta_scaled.1

/-- `(û, E)` is a relaxed subsolution for `(1 + δ) Q`. -/
theorem isParaRelaxedSub_hat : IsParaRelaxedSub U ((1 + P.δ) • Q) (Ioc 0 T) P.uhat Eset :=
  P.delta_scaled.2.2.1

/-- `v̂` is a supersolution for `(1 - δ) Q`. -/
theorem isParaSuper_hat : IsParaSuper U ((1 - P.δ) • Q) (Ioc 0 T) P.vhat :=
  P.delta_scaled.2.2.2

/-- The positivity set of `û` in `D` lies in `E`: `{p ∈ D | û p > 0} ⊆ E`. -/
theorem mem_Eset_of_uhat_pos {p : E d × ℝ} (hp : p ∈ P.D) (hpos : 0 < P.uhat p) : p ∈ Eset :=
  posSet_closedDomain_subset P.T_pos P.continuousOn_uhat P.isClosed_Eset
    P.isParaRelaxedSub_hat.2.2.2.2.1 ⟨hp, hpos⟩

/-! ### Kernels -/

theorem K_eq : P.K = P.K₀ + P.B := rfl

theorem isCompact_K₀ : IsCompact P.K₀ := isCompact_spDisk 0 _

theorem isCompact_B : IsCompact P.B := isCompact_backBall _

theorem isCompact_K : IsCompact P.K := isCompact_diskBallKernel _ _

theorem zero_mem_K₀ : (0 : E d × ℝ) ∈ P.K₀ := zero_mem_spDisk_zero P.ℓ_pos.le

theorem zero_mem_B : (0 : E d × ℝ) ∈ P.B := zero_mem_backBall _

theorem zero_mem_K : (0 : E d × ℝ) ∈ P.K := zero_mem_diskBallKernel P.ℓ_pos.le _

theorem norm_fst_le_of_mem_K₀ {k : E d × ℝ} (hk : k ∈ P.K₀) : ‖k.1‖ ≤ P.ℓ :=
  norm_fst_le_of_mem_spDisk_zero hk

theorem norm_fst_le_of_mem_B {k : E d × ℝ} (hk : k ∈ P.B) : ‖k.1‖ ≤ P.μ :=
  norm_fst_le_of_mem_backBall P.μ_pos.le hk

theorem norm_fst_le_of_mem_K {k : E d × ℝ} (hk : k ∈ P.K) : ‖k.1‖ ≤ P.lam :=
  norm_fst_le_of_mem_diskBallKernel P.μ_pos.le hk

theorem snd_mem_Icc_of_mem_B {k : E d × ℝ} (hk : k ∈ P.B) : k.2 ∈ Icc (-2 * P.μ) 0 :=
  snd_mem_Icc_of_mem_backBall P.μ_pos.le hk

theorem snd_mem_Icc_of_mem_K {k : E d × ℝ} (hk : k ∈ P.K) : k.2 ∈ Icc (-2 * P.μ) 0 :=
  snd_mem_Icc_of_mem_diskBallKernel P.μ_pos.le hk

/-- Two points of `K` are at Euclidean distance `≤ 3λ`. -/
theorem sq_dist_le_of_mem_K {k k' : E d × ℝ} (hk : k ∈ P.K) (hk' : k' ∈ P.K) :
    ‖k.1 - k'.1‖ ^ 2 + (k.2 - k'.2) ^ 2 ≤ (3 * P.lam) ^ 2 := by
  have h := sq_dist_le_of_mem_diskBallKernel P.ℓ_pos.le P.μ_pos.le hk hk'
  have : 8 * P.lam ^ 2 ≤ (3 * P.lam) ^ 2 := by nlinarith
  exact h.trans this

/-! ### The domains `U₀`, `U₁` -/

theorem isOpen_U₀ : IsOpen P.U₀ := isOpen_setOf_closedBall_subset P.isOpen _

theorem isOpen_U₁ : IsOpen P.U₁ := isOpen_setOf_closedBall_subset P.isOpen _

theorem U₀_subset : P.U₀ ⊆ U := setOf_closedBall_subset_subset P.ℓ_pos.le

theorem U₁_subset : P.U₁ ⊆ U := setOf_closedBall_subset_subset P.lam_pos.le

theorem isBounded_U₀ : Bornology.IsBounded P.U₀ := P.isBounded.subset P.U₀_subset

theorem isBounded_U₁ : Bornology.IsBounded P.U₁ := P.isBounded.subset P.U₁_subset

theorem add_mem_U_of_mem_U₀ {x y : E d} (hx : x ∈ P.U₀) (hy : ‖y‖ ≤ P.ℓ) : x + y ∈ U :=
  hx (by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left])

theorem add_mem_U_of_mem_U₁ {x y : E d} (hx : x ∈ P.U₁) (hy : ‖y‖ ≤ P.lam) : x + y ∈ U :=
  hx (by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left])

/-- `B̄_μ(x) ⊆ U₀` for `x ∈ U₁`. -/
theorem add_mem_U₀_of_mem_U₁ {x y : E d} (hx : x ∈ P.U₁) (hy : ‖y‖ ≤ P.μ) : x + y ∈ P.U₀ := by
  refine (closedBall_subset_closedBall' ?_).trans hx
  rw [dist_eq_norm, add_sub_cancel_left, lam]
  linarith

theorem U₁_subset_U₀ : P.U₁ ⊆ P.U₀ := fun x hx ↦ by
  simpa using P.add_mem_U₀_of_mem_U₁ hx (y := 0) (by simp [P.μ_pos.le])

/-! ### (a) The three convolution steps -/

/-- A convolution step from spatial inclusions and time shifts. -/
theorem convStep_of {U U' : Set (E d)} {α β α' β' r : ℝ} {K : Set (E d × ℝ)}
    (hUb : Bornology.IsBounded U) (hαβ : α < β) (hα'β' : α' < β') (hK : IsCompact K)
    (h0K : (0 : E d × ℝ) ∈ K) (hK1 : ∀ k ∈ K, ‖k.1‖ ≤ r)
    (hU' : ∀ x ∈ U', ∀ y : E d, ‖y‖ ≤ r → x + y ∈ U)
    (ht : ∀ k ∈ K, ∀ t ∈ Icc α' β', t + k.2 ∈ Icc α β)
    (ht' : ∀ k ∈ K, ∀ t ∈ Ioc α' β', t + k.2 ∈ Ioc α β) :
    ConvStep U U' α β α' β' K where
  isBounded := hUb
  lt := hαβ
  lt' := hα'β'
  isCompact := hK
  nonempty := ⟨0, h0K⟩
  closedDomain_add p hp k hk :=
    ⟨add_mem_closure_of_forall (fun y hy ↦ hU' y hy k.1 (hK1 k hk)) hp.1, ht k hk p.2 hp.2⟩
  domain_add p hp k hk := ⟨hU' p.1 hp.1 k.1 (hK1 k hk), ht' k hk p.2 hp.2⟩

/-- `(U, (0, T]) → (U₀, (0, T])` with kernel `K₀`. -/
theorem convStep_zero : ConvStep U P.U₀ 0 T 0 T P.K₀ :=
  convStep_of P.isBounded P.T_pos P.T_pos P.isCompact_K₀ P.zero_mem_K₀
    (fun _ hk ↦ P.norm_fst_le_of_mem_K₀ hk) (fun _ hx _ hy ↦ P.add_mem_U_of_mem_U₀ hx hy)
    (fun k hk t ht ↦ by rw [snd_eq_zero_of_mem_spDisk_zero hk, add_zero]; exact ht)
    (fun k hk t ht ↦ by rw [snd_eq_zero_of_mem_spDisk_zero hk, add_zero]; exact ht)

/-- `(U, (0, T]) → (U₁, (2μ, T])` with kernel `K`. -/
theorem convStep_one : ConvStep U P.U₁ 0 T (2 * P.μ) T P.K :=
  convStep_of P.isBounded P.T_pos P.two_μ_lt_T P.isCompact_K P.zero_mem_K
    (fun _ hk ↦ P.norm_fst_le_of_mem_K hk) (fun _ hx _ hy ↦ P.add_mem_U_of_mem_U₁ hx hy)
    (fun k hk t ht ↦ by
      have := P.snd_mem_Icc_of_mem_K hk
      exact ⟨by linarith [ht.1, this.1], by linarith [ht.2, this.2]⟩)
    (fun k hk t ht ↦ by
      have := P.snd_mem_Icc_of_mem_K hk
      exact ⟨by linarith [ht.1, this.1], by linarith [ht.2, this.2]⟩)

/-- `(U₀, (0, T]) → (U₁, (2μ, T])` with kernel `B`. -/
theorem convStep_zero_one : ConvStep P.U₀ P.U₁ 0 T (2 * P.μ) T P.B :=
  convStep_of P.isBounded_U₀ P.T_pos P.two_μ_lt_T P.isCompact_B P.zero_mem_B
    (fun _ hk ↦ P.norm_fst_le_of_mem_B hk) (fun _ hx _ hy ↦ P.add_mem_U₀_of_mem_U₁ hx hy)
    (fun k hk t ht ↦ by
      have := P.snd_mem_Icc_of_mem_B hk
      exact ⟨by linarith [ht.1, this.1], by linarith [ht.2, this.2]⟩)
    (fun k hk t ht ↦ by
      have := P.snd_mem_Icc_of_mem_B hk
      exact ⟨by linarith [ht.1, this.1], by linarith [ht.2, this.2]⟩)

/-! ### (b) The convolved pairs are relaxed sub / supersolutions -/

theorem lipschitzOnWith_smul_Q {a : ℝ} (ha : 0 ≤ a) :
    LipschitzOnWith (.mk a ha * P.L) (a • Q) (closure U) :=
  lipschitzOnWith_const_smul P.lipschitzOnWith ha

theorem one_add_δ_pos : 0 < 1 + P.δ := by linarith [P.δ_pos]

theorem one_sub_δ_pos : 0 < 1 - P.δ := by linarith [P.δ_le_half]

/-- `(u₀, E₀)` is a relaxed subsolution for `Q₀⁻` on `U₀ × (0, T]`. -/
theorem isParaRelaxedSub_zero : IsParaRelaxedSub P.U₀ P.Qsub₀ (Ioc 0 T) P.u₀ P.E₀ := by
  have h := P.isParaRelaxedSub_hat.supConv P.continuousOn_uhat P.convStep_zero P.zero_mem_K₀
    (fun _ hk ↦ P.norm_fst_le_of_mem_K₀ hk) (P.lipschitzOnWith_smul_Q P.one_add_δ_pos.le)
  convert h using 1
  · funext x
    simp only [Qsub₀, Pi.smul_apply, smul_eq_mul, NNReal.coe_mul, NNReal.coe_mk]
    ring
  all_goals rfl

/-- `v₀` is a supersolution for `Q₀⁺` on `U₀ × (0, T]`. -/
theorem isParaSuper_zero : IsParaSuper P.U₀ P.Qsuper₀ (Ioc 0 T) P.v₀ := by
  have h := P.isParaSuper_hat.infConv P.continuousOn_vhat P.convStep_zero P.zero_mem_K₀
    (fun _ hk ↦ P.norm_fst_le_of_mem_K₀ hk) (P.lipschitzOnWith_smul_Q P.one_sub_δ_pos.le)
  convert h using 1
  · funext x
    simp only [Qsuper₀, Pi.smul_apply, smul_eq_mul, NNReal.coe_mul, NNReal.coe_mk]
    ring
  all_goals rfl

/-- `(u₁, E₁)` is a relaxed subsolution for `Q₁⁻` on `U₁ × (2μ, T]`. -/
theorem isParaRelaxedSub_one : IsParaRelaxedSub P.U₁ P.Qsub₁ (Ioc (2 * P.μ) T) P.u₁ P.E₁ := by
  have h := P.isParaRelaxedSub_hat.supConv P.continuousOn_uhat P.convStep_one P.zero_mem_K
    (fun _ hk ↦ P.norm_fst_le_of_mem_K hk) (P.lipschitzOnWith_smul_Q P.one_add_δ_pos.le)
  convert h using 1
  · funext x
    simp only [Qsub₁, Pi.smul_apply, smul_eq_mul, NNReal.coe_mul, NNReal.coe_mk]
    ring
  all_goals rfl

/-- `v₁` is a supersolution for `Q₁⁺` on `U₁ × (2μ, T]`. -/
theorem isParaSuper_one : IsParaSuper P.U₁ P.Qsuper₁ (Ioc (2 * P.μ) T) P.v₁ := by
  have h := P.isParaSuper_hat.infConv P.continuousOn_vhat P.convStep_one P.zero_mem_K
    (fun _ hk ↦ P.norm_fst_le_of_mem_K hk) (P.lipschitzOnWith_smul_Q P.one_sub_δ_pos.le)
  convert h using 1
  · funext x
    simp only [Qsuper₁, Pi.smul_apply, smul_eq_mul, NNReal.coe_mul, NNReal.coe_mk]
    ring
  all_goals rfl

/-! ### (c) Composition -/

/-- `u₁ = u₀^B` on `D₁`. -/
theorem u₁_eq {p : E d × ℝ} (hp : p ∈ P.D₁) : P.u₁ p = supConv P.B P.u₀ p :=
  (supConv_supConv P.isCompact_K₀ ⟨0, P.zero_mem_K₀⟩ P.isCompact_B ⟨0, P.zero_mem_B⟩
    P.isCompact_D P.continuousOn_uhat P.convStep_zero.closedDomain_add
    (P.convStep_zero_one.closedDomain_add p hp)).symm

/-- `v₁ = (v₀)_B` on `D₁`. -/
theorem v₁_eq {p : E d × ℝ} (hp : p ∈ P.D₁) : P.v₁ p = infConv P.B P.v₀ p :=
  (infConv_infConv P.isCompact_K₀ ⟨0, P.zero_mem_K₀⟩ P.isCompact_B ⟨0, P.zero_mem_B⟩
    P.isCompact_D P.continuousOn_vhat P.convStep_zero.closedDomain_add
    (P.convStep_zero_one.closedDomain_add p hp)).symm

/-- `E₁ = D₁ ∩ (E₀ ⊖ B)`. -/
theorem E₁_eq : P.E₁ = setConv P.D₁ P.B P.E₀ :=
  (setConv_setConv P.convStep_zero_one.closedDomain_add).symm

/-! ### (d) Ordering -/

/-- `û ≤ u₁` on `D₁`. -/
theorem uhat_le_u₁ {p : E d × ℝ} (hp : p ∈ P.D₁) : P.uhat p ≤ P.u₁ p :=
  le_supConv_self P.isCompact_K P.zero_mem_K P.continuousOn_uhat
    (P.convStep_one.closedDomain_add p hp)

/-- `v₁ ≤ v̂` on `D₁`. -/
theorem v₁_le_vhat {p : E d × ℝ} (hp : p ∈ P.D₁) : P.v₁ p ≤ P.vhat p :=
  infConv_le_self P.isCompact_K P.zero_mem_K P.continuousOn_vhat
    (P.convStep_one.closedDomain_add p hp)

/-- `E ∩ D₁ ⊆ E₁`. -/
theorem inter_subset_E₁ : Eset ∩ P.D₁ ⊆ P.E₁ := inter_subset_setConv P.zero_mem_K

/-- `D_{ρ₀} ⊆ D₁`. -/
theorem interiorRegion_subset_D₁ : interiorRegion U T P.ρ₀ ⊆ P.D₁ := by
  rintro p ⟨hball, hρ, hT⟩
  refine ⟨subset_closure ((closedBall_subset_closedBall ?_).trans hball), ?_, hT⟩
  · linarith [P.lam_lt, P.ρ₀_pos]
  · linarith [P.two_μ_lt_ρ₀]

/-- `D₁ ⊆ D₀`. -/
theorem D₁_subset_D₀ : P.D₁ ⊆ P.D₀ := fun p hp ↦ by
  have := P.convStep_zero_one.closedDomain_add p hp 0 P.zero_mem_B
  rwa [add_zero] at this

/-- `D₀ ⊆ D`. -/
theorem D₀_subset_D : P.D₀ ⊆ P.D := fun p hp ↦ by
  have := P.convStep_zero.closedDomain_add p hp 0 P.zero_mem_K₀
  rwa [add_zero] at this

/-! ### (e) Continuity, nonnegativity, closedness, positivity sets -/

theorem continuousOn_u₀ : ContinuousOn P.u₀ P.D₀ :=
  P.convStep_zero.continuousOn_supConv P.continuousOn_uhat

theorem continuousOn_v₀ : ContinuousOn P.v₀ P.D₀ :=
  P.convStep_zero.continuousOn_infConv P.continuousOn_vhat

theorem continuousOn_u₁ : ContinuousOn P.u₁ P.D₁ :=
  P.convStep_one.continuousOn_supConv P.continuousOn_uhat

theorem continuousOn_v₁ : ContinuousOn P.v₁ P.D₁ :=
  P.convStep_one.continuousOn_infConv P.continuousOn_vhat

theorem u₀_nonneg {p : E d × ℝ} (hp : p ∈ P.D₀) : 0 ≤ P.u₀ p :=
  P.convStep_zero.supConv_nonneg P.continuousOn_uhat (fun _ hq ↦ P.uhat_nonneg hq) hp

theorem v₀_nonneg {p : E d × ℝ} (hp : p ∈ P.D₀) : 0 ≤ P.v₀ p :=
  P.convStep_zero.infConv_nonneg (fun _ hq ↦ P.vhat_nonneg hq) hp

theorem u₁_nonneg {p : E d × ℝ} (hp : p ∈ P.D₁) : 0 ≤ P.u₁ p :=
  P.convStep_one.supConv_nonneg P.continuousOn_uhat (fun _ hq ↦ P.uhat_nonneg hq) hp

theorem v₁_nonneg {p : E d × ℝ} (hp : p ∈ P.D₁) : 0 ≤ P.v₁ p :=
  P.convStep_one.infConv_nonneg (fun _ hq ↦ P.vhat_nonneg hq) hp

theorem isClosed_E₀ : IsClosed P.E₀ := P.convStep_zero.isClosed_setConv P.isClosed_Eset

theorem isClosed_E₁ : IsClosed P.E₁ := P.convStep_one.isClosed_setConv P.isClosed_Eset

theorem E₀_subset_D₀ : P.E₀ ⊆ P.D₀ := setConv_subset

theorem E₁_subset_D₁ : P.E₁ ⊆ P.D₁ := setConv_subset

theorem isCompact_D₀ : IsCompact P.D₀ := P.isBounded_U₀.isCompact_closure.prod isCompact_Icc

theorem isCompact_D₁ : IsCompact P.D₁ := P.isBounded_U₁.isCompact_closure.prod isCompact_Icc

/-- `{p ∈ D₀ | u₀ p > 0} ⊆ E₀`. -/
theorem mem_E₀_of_u₀_pos {p : E d × ℝ} (hp : p ∈ P.D₀) (hpos : 0 < P.u₀ p) : p ∈ P.E₀ :=
  posSet_closedDomain_subset P.T_pos P.continuousOn_u₀ P.isClosed_E₀
    P.isParaRelaxedSub_zero.2.2.2.2.1 ⟨hp, hpos⟩

/-- `{p ∈ D₁ | u₁ p > 0} ⊆ E₁`. -/
theorem mem_E₁_of_u₁_pos {p : E d × ℝ} (hp : p ∈ P.D₁) (hpos : 0 < P.u₁ p) : p ∈ P.E₁ :=
  posSet_closedDomain_subset P.two_μ_lt_T P.continuousOn_u₁ P.isClosed_E₁
    P.isParaRelaxedSub_one.2.2.2.2.1 ⟨hp, hpos⟩

end Config

end Crossing

end BernoulliComparison
