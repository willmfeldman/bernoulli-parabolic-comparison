/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barrier.ClosedDomain
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact

/-!
# Sup/inf-convolutions and convolution steps

For a compact nonempty kernel
`K ⊆ E d × ℝ` and `w : E d × ℝ → ℝ`:

* `supConv K w p = sup_{k ∈ K} w (p + k)` (`w^K`), `infConv K w p = inf_{k ∈ K} w (p + k)` (`w_K`);
* `reachSet K E = {p | ∃ k ∈ K, p + k ∈ E}` (the set `E ⊖_K K = E ⊕ (-K)`);
* `setConv D' K E = D' ∩ reachSet K E` (`E^K`, with target box `D'`).

A `ConvStep U U' α β α' β' K` bundles the hypotheses of a convolution step:
(H1) `D' + K ⊆ D` and (H2) `(U' × I') + K ⊆ U × I`, with `D = Ū × [α, β]`, `D' = Ū' × [α', β']`,
`I = (α, β]`, `I' = (α', β']`.

The basic properties (attainment, a modulus-of-continuity estimate, continuity, nonnegativity,
closedness, the positivity-set inclusion, and `0 ∈ K` consequences) only assume continuity of
`w` on the compact `D`, not global continuity.
-/

@[expose] public section

open Set Filter Topology Pointwise

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Definitions -/

/-- The sup-convolution `w^K(p) = sup_{k ∈ K} w (p + k)`. -/
noncomputable def supConv (K : Set (E d × ℝ)) (w : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  sSup ((fun k ↦ w (p + k)) '' K)

/-- The inf-convolution `w_K(p) = inf_{k ∈ K} w (p + k)`. -/
noncomputable def infConv (K : Set (E d × ℝ)) (w : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  sInf ((fun k ↦ w (p + k)) '' K)

/-- The reach set `E ⊖_K K = {p | (p + K) ∩ E ≠ ∅} = E ⊕ (-K)`. -/
def reachSet (K Eset : Set (E d × ℝ)) : Set (E d × ℝ) :=
  {p | ∃ k ∈ K, p + k ∈ Eset}

/-- The convolved set `E^K = D' ∩ (E ⊖_K K)` for the target box `D'`. -/
def setConv (D' K Eset : Set (E d × ℝ)) : Set (E d × ℝ) :=
  D' ∩ reachSet K Eset

/-- A convolution step `(U, (α, β]) → (U', (α', β'])` with kernel `K`:
`U` bounded, `α < β`, `α' < β'`, `K` compact and nonempty, and
(H1) `D' + K ⊆ D`, (H2) `(U' × I') + K ⊆ U × I`.
`U` and `U'` need not be open. -/
structure ConvStep (U U' : Set (E d)) (α β α' β' : ℝ) (K : Set (E d × ℝ)) : Prop where
  isBounded : Bornology.IsBounded U
  lt : α < β
  lt' : α' < β'
  isCompact : IsCompact K
  nonempty : K.Nonempty
  /-- (H1) `D' + K ⊆ D`. -/
  closedDomain_add : ∀ p ∈ closure U' ×ˢ Icc α' β', ∀ k ∈ K, p + k ∈ closure U ×ˢ Icc α β
  /-- (H2) `(U' × I') + K ⊆ U × I`. -/
  domain_add : ∀ p ∈ U' ×ˢ Ioc α' β', ∀ k ∈ K, p + k ∈ U ×ˢ Ioc α β

theorem mem_reachSet {K Eset : Set (E d × ℝ)} {p : E d × ℝ} :
    p ∈ reachSet K Eset ↔ ∃ k ∈ K, p + k ∈ Eset :=
  Iff.rfl

theorem mem_setConv {D' K Eset : Set (E d × ℝ)} {p : E d × ℝ} :
    p ∈ setConv D' K Eset ↔ p ∈ D' ∧ ∃ k ∈ K, p + k ∈ Eset :=
  Iff.rfl

/-! ### Generic properties: a kernel translate inside a set where `w` is continuous -/

section Generic

variable {K S : Set (E d × ℝ)} {w : E d × ℝ → ℝ} {p p' : E d × ℝ}

theorem continuousOn_comp_add (hw : ContinuousOn w S) (hp : ∀ k ∈ K, p + k ∈ S) :
    ContinuousOn (fun k ↦ w (p + k)) K :=
  hw.comp (continuous_const.add continuous_id).continuousOn (fun k hk ↦ hp k hk)

theorem bddAbove_image_add (hK : IsCompact K) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) : BddAbove ((fun k ↦ w (p + k)) '' K) :=
  hK.bddAbove_image (continuousOn_comp_add hw hp)

theorem bddBelow_image_add (hK : IsCompact K) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) : BddBelow ((fun k ↦ w (p + k)) '' K) :=
  hK.bddBelow_image (continuousOn_comp_add hw hp)

/-- `w (p + k) ≤ w^K(p)` for `k ∈ K`. -/
theorem le_supConv (hK : IsCompact K) (hw : ContinuousOn w S) (hp : ∀ k ∈ K, p + k ∈ S)
    {k : E d × ℝ} (hk : k ∈ K) : w (p + k) ≤ supConv K w p :=
  le_csSup (bddAbove_image_add hK hw hp) ⟨k, hk, rfl⟩

/-- `w_K(p) ≤ w (p + k)` for `k ∈ K`. -/
theorem infConv_le (hK : IsCompact K) (hw : ContinuousOn w S) (hp : ∀ k ∈ K, p + k ∈ S)
    {k : E d × ℝ} (hk : k ∈ K) : infConv K w p ≤ w (p + k) :=
  csInf_le (bddBelow_image_add hK hw hp) ⟨k, hk, rfl⟩

theorem supConv_le (hne : K.Nonempty) {c : ℝ} (h : ∀ k ∈ K, w (p + k) ≤ c) :
    supConv K w p ≤ c :=
  csSup_le (hne.image _) (by rintro _ ⟨k, hk, rfl⟩; exact h k hk)

theorem le_infConv (hne : K.Nonempty) {c : ℝ} (h : ∀ k ∈ K, c ≤ w (p + k)) :
    c ≤ infConv K w p :=
  le_csInf (hne.image _) (by rintro _ ⟨k, hk, rfl⟩; exact h k hk)

/-- The sup in `w^K(p)` is attained. -/
theorem exists_supConv_eq (hK : IsCompact K) (hne : K.Nonempty) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) : ∃ k ∈ K, supConv K w p = w (p + k) := by
  obtain ⟨k, hk, hmax⟩ := hK.exists_isMaxOn hne (continuousOn_comp_add hw hp)
  exact ⟨k, hk, le_antisymm (supConv_le hne fun k' hk' ↦ hmax hk') (le_supConv hK hw hp hk)⟩

/-- The inf in `w_K(p)` is attained. -/
theorem exists_infConv_eq (hK : IsCompact K) (hne : K.Nonempty) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) : ∃ k ∈ K, infConv K w p = w (p + k) := by
  obtain ⟨k, hk, hmin⟩ := hK.exists_isMinOn hne (continuousOn_comp_add hw hp)
  exact ⟨k, hk, le_antisymm (infConv_le hK hw hp hk) (le_infConv hne fun k' hk' ↦ hmin hk')⟩

/-- Modulus of continuity of the sup-convolution: if `|w (p + k) - w (p' + k)| ≤ c` for all
`k ∈ K`, then `|w^K(p) - w^K(p')| ≤ c`. -/
theorem abs_supConv_sub_le (hK : IsCompact K) (hne : K.Nonempty) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) (hp' : ∀ k ∈ K, p' + k ∈ S) {c : ℝ}
    (hc : ∀ k ∈ K, |w (p + k) - w (p' + k)| ≤ c) :
    |supConv K w p - supConv K w p'| ≤ c := by
  obtain ⟨k, hk, hkeq⟩ := exists_supConv_eq hK hne hw hp
  obtain ⟨k', hk', hk'eq⟩ := exists_supConv_eq hK hne hw hp'
  have h1 := le_supConv hK hw hp' hk
  have h2 := le_supConv hK hw hp hk'
  have e1 := (abs_le.mp (hc k hk))
  have e2 := (abs_le.mp (hc k' hk'))
  rw [abs_le]
  constructor <;> linarith

/-- Modulus of continuity of the inf-convolution `w_K`. -/
theorem abs_infConv_sub_le (hK : IsCompact K) (hne : K.Nonempty) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) (hp' : ∀ k ∈ K, p' + k ∈ S) {c : ℝ}
    (hc : ∀ k ∈ K, |w (p + k) - w (p' + k)| ≤ c) :
    |infConv K w p - infConv K w p'| ≤ c := by
  obtain ⟨k, hk, hkeq⟩ := exists_infConv_eq hK hne hw hp
  obtain ⟨k', hk', hk'eq⟩ := exists_infConv_eq hK hne hw hp'
  have h1 := infConv_le hK hw hp' hk
  have h2 := infConv_le hK hw hp hk'
  have e1 := (abs_le.mp (hc k hk))
  have e2 := (abs_le.mp (hc k' hk'))
  rw [abs_le]
  constructor <;> linarith

/-- Uniform continuity of the sup-convolution: if `w` is continuous on a compact `S` and
`p + K ⊆ S` for all `p ∈ D'`, then `w^K` is uniformly continuous on `D'` (with the modulus of
`w` on `S`). -/
theorem uniformContinuousOn_supConv {D' : Set (E d × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (hS : IsCompact S) (hw : ContinuousOn w S) (hD' : ∀ p ∈ D', ∀ k ∈ K, p + k ∈ S) :
    UniformContinuousOn (supConv K w) D' := by
  have hu := Metric.uniformContinuousOn_iff_le.mp (hS.uniformContinuousOn_of_continuous hw)
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨δ, hδ, fun p hp p' hp' hpp' ↦ ?_⟩
  rw [Real.dist_eq]
  refine abs_supConv_sub_le hK hne hw (hD' p hp) (hD' p' hp') fun k hk ↦ ?_
  rw [← Real.dist_eq]
  exact h _ (hD' p hp k hk) _ (hD' p' hp' k hk) (by rwa [dist_add_right])

/-- Uniform continuity of the inf-convolution `w_K`. -/
theorem uniformContinuousOn_infConv {D' : Set (E d × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (hS : IsCompact S) (hw : ContinuousOn w S) (hD' : ∀ p ∈ D', ∀ k ∈ K, p + k ∈ S) :
    UniformContinuousOn (infConv K w) D' := by
  have hu := Metric.uniformContinuousOn_iff_le.mp (hS.uniformContinuousOn_of_continuous hw)
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨δ, hδ, fun p hp p' hp' hpp' ↦ ?_⟩
  rw [Real.dist_eq]
  refine abs_infConv_sub_le hK hne hw (hD' p hp) (hD' p' hp') fun k hk ↦ ?_
  rw [← Real.dist_eq]
  exact h _ (hD' p hp k hk) _ (hD' p' hp' k hk) (by rwa [dist_add_right])

/-- `w^K(p) ≥ 0` if `w ≥ 0` on a set `S` containing `p + K`. -/
theorem supConv_nonneg (hK : IsCompact K) (hne : K.Nonempty) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) (h0 : ∀ q ∈ S, 0 ≤ w q) : 0 ≤ supConv K w p := by
  obtain ⟨k, hk⟩ := hne
  exact (h0 _ (hp k hk)).trans (le_supConv hK hw hp hk)

/-- `w_K(p) ≥ 0` if `w ≥ 0` on a set `S` containing `p + K`. -/
theorem infConv_nonneg (hne : K.Nonempty) (hp : ∀ k ∈ K, p + k ∈ S) (h0 : ∀ q ∈ S, 0 ≤ w q) :
    0 ≤ infConv K w p :=
  le_infConv hne fun k hk ↦ h0 _ (hp k hk)

/-- If `0 ∈ K` then `w ≤ w^K`. -/
theorem le_supConv_self (hK : IsCompact K) (h0K : (0 : E d × ℝ) ∈ K) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) : w p ≤ supConv K w p := by
  simpa using le_supConv hK hw hp h0K

/-- If `0 ∈ K` then `w_K ≤ w`. -/
theorem infConv_le_self (hK : IsCompact K) (h0K : (0 : E d × ℝ) ∈ K) (hw : ContinuousOn w S)
    (hp : ∀ k ∈ K, p + k ∈ S) : infConv K w p ≤ w p := by
  simpa using infConv_le hK hw hp h0K

/-- If `{w > 0} ∩ S ⊆ Θ` and `w^K(p) > 0`, every maximizer
`p + k` lies in `Θ`. -/
theorem add_mem_of_supConv_pos {Θ : Set (E d × ℝ)} (hΘ : ∀ q ∈ S, 0 < w q → q ∈ Θ)
    (hp : ∀ k ∈ K, p + k ∈ S) {k : E d × ℝ} (hk : k ∈ K) (hkeq : supConv K w p = w (p + k))
    (hpos : 0 < supConv K w p) : p + k ∈ Θ :=
  hΘ _ (hp k hk) (hkeq ▸ hpos)

end Generic

/-! ### The sets `E ⊖_K K` and `E^K` -/

theorem reachSet_eq_add_neg (K Eset : Set (E d × ℝ)) : reachSet K Eset = Eset + -K := by
  ext p
  simp only [mem_reachSet, Set.mem_add, Set.mem_neg]
  constructor
  · rintro ⟨k, hk, hpk⟩
    exact ⟨p + k, hpk, -k, by simpa using hk, by abel⟩
  · rintro ⟨e, he, k', hk', rfl⟩
    exact ⟨-k', hk', by simpa using he⟩

/-- `E ⊖_K K` is closed for `E` closed and `K` compact. -/
theorem isClosed_reachSet {K Eset : Set (E d × ℝ)} (hK : IsCompact K) (hE : IsClosed Eset) :
    IsClosed (reachSet K Eset) := by
  rw [reachSet_eq_add_neg]
  exact hE.add_right_of_isCompact hK.neg

/-- `E^K` is closed. -/
theorem isClosed_setConv {D' K Eset : Set (E d × ℝ)} (hD' : IsClosed D') (hK : IsCompact K)
    (hE : IsClosed Eset) : IsClosed (setConv D' K Eset) :=
  hD'.inter (isClosed_reachSet hK hE)

theorem setConv_subset {D' K Eset : Set (E d × ℝ)} : setConv D' K Eset ⊆ D' :=
  inter_subset_left

/-- If `0 ∈ K` then `E ∩ D' ⊆ E^K`. -/
theorem inter_subset_setConv {D' K Eset : Set (E d × ℝ)} (h0K : (0 : E d × ℝ) ∈ K) :
    Eset ∩ D' ⊆ setConv D' K Eset :=
  fun p hp ↦ ⟨hp.2, 0, h0K, by simpa using hp.1⟩

theorem mem_reachSet_of_add_mem {K Eset : Set (E d × ℝ)} {p k : E d × ℝ} (hk : k ∈ K)
    (hpk : p + k ∈ Eset) : p ∈ reachSet K Eset :=
  ⟨k, hk, hpk⟩

/-! ### Convolution steps -/

namespace ConvStep

variable {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}

/-- The source box `D = Ū × [α, β]` of a convolution step is compact. -/
theorem isCompact_closedDomain (hS : ConvStep U U' α β α' β' K) :
    IsCompact (closure U ×ˢ Icc α β) :=
  hS.isBounded.isCompact_closure.prod isCompact_Icc

theorem isClosed_closedDomain' (_hS : ConvStep U U' α β α' β' K) :
    IsClosed (closure U' ×ˢ Icc α' β') :=
  isClosed_closure.prod isClosed_Icc

/-- `w^K` is continuous on `D'` if `w` is continuous on `D`. -/
theorem continuousOn_supConv (hS : ConvStep U U' α β α' β' K) {w : E d × ℝ → ℝ}
    (hw : ContinuousOn w (closure U ×ˢ Icc α β)) :
    ContinuousOn (supConv K w) (closure U' ×ˢ Icc α' β') :=
  (uniformContinuousOn_supConv hS.isCompact hS.nonempty hS.isCompact_closedDomain hw
    hS.closedDomain_add).continuousOn

/-- `w_K` is continuous on `D'` if `w` is continuous on `D`. -/
theorem continuousOn_infConv (hS : ConvStep U U' α β α' β' K) {w : E d × ℝ → ℝ}
    (hw : ContinuousOn w (closure U ×ˢ Icc α β)) :
    ContinuousOn (infConv K w) (closure U' ×ˢ Icc α' β') :=
  (uniformContinuousOn_infConv hS.isCompact hS.nonempty hS.isCompact_closedDomain hw
    hS.closedDomain_add).continuousOn

/-- `w^K ≥ 0` on `D'` if `w ≥ 0` on `D`. -/
theorem supConv_nonneg (hS : ConvStep U U' α β α' β' K) {w : E d × ℝ → ℝ}
    (hw : ContinuousOn w (closure U ×ˢ Icc α β)) (h0 : ∀ q ∈ closure U ×ˢ Icc α β, 0 ≤ w q)
    {p : E d × ℝ} (hp : p ∈ closure U' ×ˢ Icc α' β') : 0 ≤ supConv K w p :=
  BernoulliComparison.supConv_nonneg hS.isCompact hS.nonempty hw (hS.closedDomain_add p hp) h0

/-- `w_K ≥ 0` on `D'` if `w ≥ 0` on `D`. -/
theorem infConv_nonneg (hS : ConvStep U U' α β α' β' K) {w : E d × ℝ → ℝ}
    (h0 : ∀ q ∈ closure U ×ˢ Icc α β, 0 ≤ w q)
    {p : E d × ℝ} (hp : p ∈ closure U' ×ˢ Icc α' β') : 0 ≤ infConv K w p :=
  BernoulliComparison.infConv_nonneg hS.nonempty (hS.closedDomain_add p hp) h0

/-- `E^K` is closed and lies in `D' = closure (U' × I')`. -/
theorem isClosed_setConv (hS : ConvStep U U' α β α' β' K) {Eset : Set (E d × ℝ)}
    (hE : IsClosed Eset) : IsClosed (setConv (closure U' ×ˢ Icc α' β') K Eset) :=
  BernoulliComparison.isClosed_setConv hS.isClosed_closedDomain' hS.isCompact hE

/-- `E^K ⊆ Ū' × Ī'`. -/
theorem setConv_subset_closure (hS : ConvStep U U' α β α' β' K) {Eset : Set (E d × ℝ)} :
    setConv (closure U' ×ˢ Icc α' β') K Eset ⊆ closure U' ×ˢ closure (Ioc α' β') := by
  rw [closure_Ioc hS.lt'.ne]
  exact setConv_subset

/-- If `{w > 0} ∩ (U × I) ⊆ E` then `{w^K > 0} ∩ (U' × I') ⊆ E^K`. -/
theorem posSetP_supConv_subset (hS : ConvStep U U' α β α' β' K) {w : E d × ℝ → ℝ}
    (hw : ContinuousOn w (closure U ×ˢ Icc α β)) {Eset : Set (E d × ℝ)}
    (hsub : posSetP w (U ×ˢ Ioc α β) ⊆ Eset) :
    posSetP (supConv K w) (U' ×ˢ Ioc α' β') ⊆ setConv (closure U' ×ˢ Icc α' β') K Eset := by
  rintro p ⟨hp, hpos⟩
  have hpD : p ∈ closure U' ×ˢ Icc α' β' := prod_Ioc_subset_closure hp
  obtain ⟨k, hk, hkeq⟩ := exists_supConv_eq hS.isCompact hS.nonempty hw
    (hS.closedDomain_add p hpD)
  exact ⟨hpD, k, hk, hsub ⟨hS.domain_add p hp k hk, hkeq ▸ hpos⟩⟩

end ConvStep

end BernoulliComparison
