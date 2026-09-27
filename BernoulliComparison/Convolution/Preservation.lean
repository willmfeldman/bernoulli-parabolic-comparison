/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Convolution.Basic
public import BernoulliComparison.Barrier.Classical

/-!
# Preservation of the solution classes under sup/inf-convolution

In a convolution step (`ConvStep`) with `0 ∈ K` and spatial
radius `ℓ` (`‖k.1‖ ≤ ℓ` on `K`), and `Q` `L`-Lipschitz on `Ū`:

* if `(u, E)` is a relaxed subsolution for `Q` on `U × (α, β]` and `u` is continuous on
  `D = Ū × [α, β]`, then `(u^K, E^K)` is a relaxed subsolution for `Q - Lℓ` on `U' × (α', β']`
  (`IsParaRelaxedSub.supConv`);
* if `v` is a supersolution for `Q` on `U × (α, β]`, continuous on `D`, then `v_K` is a
  supersolution for `Q + Lℓ` on `U' × (α', β']` (`IsParaSuper.infConv`).

Both are proved directly from the barrier definitions, using the classical-barrier translation
lemmas of `Barrier/Classical.lean` (`IsClassicalStrictParaSuper.translate`,
`IsClassicalStrictParaSub.translate`, `AdmissibleCyl.translate`); they do not use the
solution-level translation lemmas.
-/

@[expose] public section

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Translation of cylinders, parabolic boundaries and positivity sets (membership form) -/

theorem mem_image_add_right_iff {A : Type*} [AddGroup A] {c x : A} {S : Set A} :
    x ∈ (· + c) '' S ↔ x - c ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x - c, h, sub_add_cancel x c⟩

/-- A point lies in a translated parabolic boundary iff its back-translate lies in the original. -/
theorem mem_parBdry_translate {V : Set (E d)} {a b : ℝ} {k q : E d × ℝ} :
    q ∈ parBdry ((· + k.1) '' V) (a + k.2) (b + k.2) ↔ q - k ∈ parBdry V a b := by
  simp only [parBdry, ← image_add_closure, ← image_add_frontier, mem_union, mem_prod,
    mem_image_add_right_iff, mem_singleton_iff, mem_Icc, Prod.fst_sub, Prod.snd_sub]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, by linarith⟩
    · exact Or.inr ⟨h1, by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, by linarith⟩
    · exact Or.inr ⟨h1, by linarith, by linarith⟩

/-- A point lies in a translated cylinder iff its back-translate lies in the original. -/
theorem mem_cyl_translate {V : Set (E d)} {a b : ℝ} {k q : E d × ℝ} :
    q ∈ cyl ((· + k.1) '' V) (a + k.2) (b + k.2) ↔ q - k ∈ cyl V a b := by
  simp only [cyl, mem_prod, mem_image_add_right_iff, mem_Ioc, Prod.fst_sub, Prod.snd_sub]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩

/-- The closure of the positivity set of a translate `φ (· - k)` is the translate of the closure. -/
theorem mem_closure_posSetP_comp_sub {φ : E d × ℝ → ℝ} {k q : E d × ℝ} :
    q ∈ closure (posSetP (fun q ↦ φ (q - k)) univ) ↔ q - k ∈ closure (posSetP φ univ) := by
  have h : posSetP (fun q ↦ φ (q - k)) univ = (Homeomorph.subRight k) ⁻¹' posSetP φ univ := by
    ext q
    simp [posSetP]
  rw [h, ← Homeomorph.preimage_closure]
  rfl

/-- The parabolic boundary of an admissible cylinder lies in the domain. -/
theorem AdmissibleCyl.parBdry_subset {U : Set (E d)} {I : Set ℝ} {V : Set (E d)} {a b : ℝ}
    (h : AdmissibleCyl U I V a b) : parBdry V a b ⊆ U ×ˢ I := by
  refine union_subset (fun p hp ↦ h.2.2.2 ⟨hp.1, ?_⟩) (fun p hp ↦ h.2.2.2
    ⟨frontier_subset_closure hp.1, hp.2⟩)
  rw [mem_singleton_iff.mp hp.2]
  exact ⟨le_rfl, h.2.2.1.le⟩

/-- An admissible cylinder lies in the domain. -/
theorem AdmissibleCyl.cyl_subset {U : Set (E d)} {I : Set ℝ} {V : Set (E d)} {a b : ℝ}
    (h : AdmissibleCyl U I V a b) : cyl V a b ⊆ U ×ˢ I :=
  fun _ hp ↦ h.2.2.2 ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩

/-! ### The Lipschitz error of a translated `Q` -/

namespace ConvStep

variable {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}

/-- In a convolution step with `0 ∈ K` and spatial radius `ℓ`, for an admissible cylinder
`V × (a, b]` of `U' × I'` and `k ∈ K`, both `x` and `x + k.1` lie in `U` for `x ∈ V̄`; so a
`Q` that is `L`-Lipschitz on `Ū` changes by at most `Lℓ`. -/
theorem abs_sub_le_of_lipschitzOnWith (hS : ConvStep U U' α β α' β' K)
    (h0K : (0 : E d × ℝ) ∈ K) {ℓ : ℝ} (hKℓ : ∀ k ∈ K, ‖k.1‖ ≤ ℓ) {Q : E d → ℝ} {L : NNReal}
    (hQ : LipschitzOnWith L Q (closure U)) {V : Set (E d)} {a b : ℝ}
    (hVab : AdmissibleCyl U' (Ioc α' β') V a b) {k : E d × ℝ} (hk : k ∈ K) {x : E d}
    (hx : x ∈ closure V) : |Q (x + k.1) - Q x| ≤ L * ℓ := by
  have hxa : ((x, a) : E d × ℝ) ∈ U' ×ˢ Ioc α' β' :=
    hVab.2.2.2 ⟨hx, le_rfl, hVab.2.2.1.le⟩
  have h1 := (hS.domain_add _ hxa k hk).1
  have h0 := (hS.domain_add _ hxa 0 h0K).1
  simp only [Prod.fst_add, add_zero] at h1 h0
  have := hQ.dist_le_mul _ (subset_closure h1) _ (subset_closure h0)
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
  exact this.trans (mul_le_mul_of_nonneg_left (hKℓ k hk) L.2)

end ConvStep

/-! ### Sup-convolution of relaxed subsolutions -/

/-- Sup-convolution preserves relaxed subsolutions. In a convolution step with `0 ∈ K` and
spatial radius `ℓ`, if `Q` is `L`-Lipschitz on `Ū`, `(u, E)` is a relaxed subsolution for `Q`
on `U × (α, β]` and `u` is continuous on `Ū × [α, β]`, then `(u^K, E^K)` is a relaxed
subsolution for `Q - Lℓ` on `U' × (α', β']`, where `E^K = setConv (Ū' × [α', β']) K E`. -/
theorem IsParaRelaxedSub.supConv {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}
    {Q : E d → ℝ} {u : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)} {L : NNReal} {ℓ : ℝ}
    (hu : IsParaRelaxedSub U Q (Ioc α β) u Eset) (hcont : ContinuousOn u (closure U ×ˢ Icc α β))
    (hS : ConvStep U U' α β α' β' K) (h0K : (0 : E d × ℝ) ∈ K) (hKℓ : ∀ k ∈ K, ‖k.1‖ ≤ ℓ)
    (hQ : LipschitzOnWith L Q (closure U)) :
    IsParaRelaxedSub U' (fun x ↦ Q x - L * ℓ) (Ioc α' β') (BernoulliComparison.supConv K u)
      (setConv (closure U' ×ˢ Icc α' β') K Eset) := by
  obtain ⟨-, hnn, hEc, -, hpos, hR6⟩ := hu
  have hnnD : ∀ q ∈ closure U ×ˢ Icc α β, 0 ≤ u q := nonneg_on_closedDomain hS.lt hcont hnn
  refine ⟨(hS.continuousOn_supConv hcont).mono prod_Ioc_subset_closure,
    fun p hp ↦ hS.supConv_nonneg hcont hnnD (prod_Ioc_subset_closure hp),
    hS.isClosed_setConv hEc, hS.setConv_subset_closure, hS.posSetP_supConv_subset hcont hpos, ?_⟩
  intro V a b φ hVab hφ hbd
  -- Steps 1–2: for each `k ∈ K`, the translate `φ (· - k)` is a barrier for `Q` on the
  -- translated cylinder, and `u < φ (· - k)` on `E ∩ cyl (V + k)`.
  have hstep : ∀ k ∈ K,
      PrecOn u (fun q ↦ φ (q - k)) Eset (cyl ((· + k.1) '' V) (a + k.2) (b + k.2)) := by
    intro k hk
    have hadm : AdmissibleCyl U (Ioc α β) ((· + k.1) '' V) (a + k.2) (b + k.2) :=
      hVab.translate k (by rintro _ ⟨p, hp, rfl⟩; exact hS.domain_add p hp k hk)
    have hφk : IsClassicalStrictParaSuper Q (fun q ↦ φ (q - k)) ((· + k.1) '' V)
        (a + k.2) (b + k.2) := by
      refine hφ.translate k fun x hx ↦ ?_
      have := (abs_le.mp (hS.abs_sub_le_of_lipschitzOnWith h0K hKℓ hQ hVab hk hx)).1
      linarith
    refine hR6 _ _ _ _ hadm hφk ?_
    rintro q ⟨hqE, hqP⟩
    rw [mem_parBdry_translate] at hqP
    have hpD : q - k ∈ closure U' ×ˢ Icc α' β' :=
      prod_Ioc_subset_closure (hVab.parBdry_subset hqP)
    have hq : q - k + k = q := sub_add_cancel q k
    have hmem : q - k ∈ setConv (closure U' ×ˢ Icc α' β') K Eset :=
      ⟨hpD, k, hk, by rwa [hq]⟩
    calc u q = u (q - k + k) := by rw [hq]
      _ ≤ BernoulliComparison.supConv K u (q - k) :=
          le_supConv hS.isCompact hcont (hS.closedDomain_add _ hpD) hk
      _ < φ (q - k) := hbd _ ⟨hmem, hqP⟩
  -- Step 3: interior.
  rintro p ⟨hpE, hpC⟩
  have hpUI : p ∈ U' ×ˢ Ioc α' β' := hVab.cyl_subset hpC
  have hpD : p ∈ closure U' ×ˢ Icc α' β' := prod_Ioc_subset_closure hpUI
  have hcylk : ∀ k : E d × ℝ, p + k ∈ cyl ((· + k.1) '' V) (a + k.2) (b + k.2) := fun k ↦
    mem_cyl_translate.2 (by rwa [add_sub_cancel_right])
  obtain ⟨k, hk, hkeq⟩ := exists_supConv_eq hS.isCompact hS.nonempty hcont
    (hS.closedDomain_add p hpD)
  rw [hkeq]
  rcases lt_or_ge 0 (u (p + k)) with hpos' | hnpos
  · have := hstep k hk (p + k) ⟨hpos ⟨hS.domain_add p hpUI k hk, hpos'⟩, hcylk k⟩
    simpa using this
  · obtain ⟨k₀, hk₀, hk₀E⟩ := hpE.2
    have h1 := hstep k₀ hk₀ (p + k₀) ⟨hk₀E, hcylk k₀⟩
    simp only [add_sub_cancel_right] at h1
    have h2 := hnnD _ (hS.closedDomain_add p hpD k₀ hk₀)
    linarith

/-! ### Inf-convolution of supersolutions -/

/-- Inf-convolution preserves supersolutions. In a convolution step with `0 ∈ K` and spatial
radius `ℓ`, if `Q` is `L`-Lipschitz on `Ū` and `v` is a supersolution for `Q` on
`U × (α, β]`, continuous on `Ū × [α, β]`, then `v_K` is a supersolution for `Q + Lℓ` on
`U' × (α', β']`. -/
theorem IsParaSuper.infConv {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}
    {Q : E d → ℝ} {v : E d × ℝ → ℝ} {L : NNReal} {ℓ : ℝ}
    (hv : IsParaSuper U Q (Ioc α β) v) (hcont : ContinuousOn v (closure U ×ˢ Icc α β))
    (hS : ConvStep U U' α β α' β' K) (h0K : (0 : E d × ℝ) ∈ K) (hKℓ : ∀ k ∈ K, ‖k.1‖ ≤ ℓ)
    (hQ : LipschitzOnWith L Q (closure U)) :
    IsParaSuper U' (fun x ↦ Q x + L * ℓ) (Ioc α' β') (BernoulliComparison.infConv K v) := by
  obtain ⟨-, hnn, hR6⟩ := hv
  have hnnD : ∀ q ∈ closure U ×ˢ Icc α β, 0 ≤ v q := nonneg_on_closedDomain hS.lt hcont hnn
  refine ⟨(hS.continuousOn_infConv hcont).mono prod_Ioc_subset_closure,
    fun p hp ↦ hS.infConv_nonneg hnnD (prod_Ioc_subset_closure hp), ?_⟩
  intro V a b φ hVab hφ hbd
  have hstep : ∀ k ∈ K,
      Prec (fun q ↦ φ (q - k)) v univ (cyl ((· + k.1) '' V) (a + k.2) (b + k.2)) := by
    intro k hk
    have hadm : AdmissibleCyl U (Ioc α β) ((· + k.1) '' V) (a + k.2) (b + k.2) :=
      hVab.translate k (by rintro _ ⟨p, hp, rfl⟩; exact hS.domain_add p hp k hk)
    have hφk : IsClassicalStrictParaSub Q (fun q ↦ φ (q - k)) ((· + k.1) '' V)
        (a + k.2) (b + k.2) := by
      refine hφ.translate k fun x hx ↦ ?_
      have := (abs_le.mp (hS.abs_sub_le_of_lipschitzOnWith h0K hKℓ hQ hVab hk hx)).2
      linarith
    refine hR6 _ _ _ _ hadm hφk ?_
    rintro q ⟨hqE, hqP⟩
    rw [mem_closure_posSetP_comp_sub] at hqE
    rw [mem_parBdry_translate] at hqP
    have hpD : q - k ∈ closure U' ×ˢ Icc α' β' :=
      prod_Ioc_subset_closure (hVab.parBdry_subset hqP)
    have hq : q - k + k = q := sub_add_cancel q k
    calc φ (q - k) < BernoulliComparison.infConv K v (q - k) := hbd _ ⟨hqE, hqP⟩
      _ ≤ v (q - k + k) := infConv_le hS.isCompact hcont (hS.closedDomain_add _ hpD) hk
      _ = v q := by rw [hq]
  rintro p ⟨hpE, hpC⟩
  have hpUI : p ∈ U' ×ˢ Ioc α' β' := hVab.cyl_subset hpC
  have hpD : p ∈ closure U' ×ˢ Icc α' β' := prod_Ioc_subset_closure hpUI
  obtain ⟨k, hk, hkeq⟩ := exists_infConv_eq hS.isCompact hS.nonempty hcont
    (hS.closedDomain_add p hpD)
  rw [hkeq]
  have hcyl : p + k ∈ cyl ((· + k.1) '' V) (a + k.2) (b + k.2) :=
    mem_cyl_translate.2 (by rwa [add_sub_cancel_right])
  have hcl : p + k ∈ closure (posSetP (fun q ↦ φ (q - k)) univ) :=
    mem_closure_posSetP_comp_sub.2 (by rwa [add_sub_cancel_right])
  have := hstep k hk (p + k) ⟨hcl, hcyl⟩
  simpa using this

end BernoulliComparison
