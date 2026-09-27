/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Barrier.Classical

/-!
# Barrier toolkit: structural lemmas for the solution classes

Monotonicity in `Q`, positive scaling, translation, and restriction to a smaller domain for
`IsParaRelaxedSub` and `IsParaSuper`, proved directly from the barrier definitions. Scaling is
used for the δ-scaling in `Barrier/Margin.lean`.
-/

@[expose] public section

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

/-! ### Monotonicity in `Q` -/

/-- Decreasing `Q` keeps `(u, E)` a relaxed subsolution: the barrier
clause is quantified over classical strict supersolutions of `Q`, and shrinking `Q` to `Q'` only
shrinks that family (`IsClassicalStrictParaSuper.mono_Q`). -/
theorem IsParaRelaxedSub.mono_Q {U : Set (E d)} {Q Q' : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    {Eset : Set (E d × ℝ)} (h : IsParaRelaxedSub U Q I u Eset) (hQ : ∀ x, Q' x ≤ Q x) :
    IsParaRelaxedSub U Q' I u Eset := by
  obtain ⟨hcont, hnonneg, hclosed, hsub, hpos, hbar⟩ := h
  exact ⟨hcont, hnonneg, hclosed, hsub, hpos,
    fun V a b φ hVab hφ' hprec ↦ hbar V a b φ hVab (hφ'.mono_Q hQ) hprec⟩

/-- Increasing `Q` keeps `u` a supersolution: the barrier clause is
quantified over classical strict subsolutions of `Q`, and growing `Q` to `Q'` only shrinks that
family (`IsClassicalStrictParaSub.mono_Q`). -/
theorem IsParaSuper.mono_Q {U : Set (E d)} {Q Q' : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    (h : IsParaSuper U Q I u) (hQ : ∀ x, Q x ≤ Q' x) :
    IsParaSuper U Q' I u := by
  obtain ⟨hcont, hnonneg, hbar⟩ := h
  exact ⟨hcont, hnonneg, fun V a b φ hVab hφ' hprec ↦ hbar V a b φ hVab (hφ'.mono_Q hQ) hprec⟩

/-! ### Positive scaling -/

/-- `(u, E)` a relaxed subsolution for `Q` gives `(c • u, E)` a relaxed subsolution for `c • Q`,
`c > 0`. -/
theorem IsParaRelaxedSub.smul {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    {Eset : Set (E d × ℝ)} (h : IsParaRelaxedSub U Q I u Eset) {c : ℝ} (hc : 0 < c) :
    IsParaRelaxedSub U (c • Q) I (c • u) Eset := by
  obtain ⟨hcont, hnonneg, hclosed, hsub, hpos, hbar⟩ := h
  refine ⟨hcont.const_smul c, fun p hp ↦ mul_nonneg hc.le (hnonneg p hp), hclosed, hsub, ?_, ?_⟩
  · rw [posSetP_const_smul_of_pos hc]; exact hpos
  · intro V a b φ hVab hφ hprec
    set ψ : E d × ℝ → ℝ := c⁻¹ • φ with hψdef
    have hψbar : IsClassicalStrictParaSuper Q ψ V a b :=
      (IsClassicalStrictParaSuper.smul_iff hc).mp hφ
    have hφeq : φ = c • ψ := by rw [hψdef, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [hφeq, PrecOn.smul_iff hc] at hprec
    have := hbar V a b ψ hVab hψbar hprec
    rwa [hφeq, PrecOn.smul_iff hc]

/-- `u` a supersolution for `Q` gives `c • u` a supersolution for `c • Q`,
`c > 0`. -/
theorem IsParaSuper.smul {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    (h : IsParaSuper U Q I u) {c : ℝ} (hc : 0 < c) :
    IsParaSuper U (c • Q) I (c • u) := by
  obtain ⟨hcont, hnonneg, hbar⟩ := h
  refine ⟨hcont.const_smul c, fun p hp ↦ mul_nonneg hc.le (hnonneg p hp), ?_⟩
  intro V a b φ hVab hφ hprec
  set ψ : E d × ℝ → ℝ := c⁻¹ • φ with hψdef
  have hψbar : IsClassicalStrictParaSub Q ψ V a b :=
    (IsClassicalStrictParaSub.smul_iff hc).mp hφ
  have hφeq : φ = c • ψ := by rw [hψdef, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [hφeq, Prec.smul_iff hc] at hprec
  have := hbar V a b ψ hVab hψbar hprec
  rwa [hφeq, Prec.smul_iff hc]

/-! ### Space-time translation -/

/-- The parabolic boundary translates with the cylinder. -/
theorem image_add_parBdry (V : Set (E d)) (a b : ℝ) (c : E d × ℝ) :
    (fun q ↦ q + c) '' parBdry V a b = parBdry ((· + c.1) '' V) (a + c.2) (b + c.2) := by
  unfold parBdry
  rw [image_union, image_add_prod, image_add_prod, image_add_closure, image_add_frontier,
    image_singleton, image_add_right_Icc]

/-- The cylinder `V × (a, b]` translates componentwise. -/
theorem image_add_cyl (V : Set (E d)) (a b : ℝ) (c : E d × ℝ) :
    (fun q ↦ q + c) '' cyl V a b = cyl ((· + c.1) '' V) (a + c.2) (b + c.2) := by
  unfold cyl
  rw [image_add_prod, image_add_const_Ioc]

/-- The closed positivity set of a translate is the translate of the closed positivity set. -/
theorem closure_posSetP_univ_comp_sub (φ : E d × ℝ → ℝ) (c : E d × ℝ) :
    closure (posSetP (fun q ↦ φ (q - c)) univ) = (fun q ↦ q + c) '' closure (posSetP φ univ) := by
  have h : posSetP (fun q ↦ φ (q - c)) univ = (fun q ↦ q + c) '' posSetP φ univ := by
    simpa [posSetP] using posSet_comp_sub_eq c φ
  rw [h, image_add_closure]

/-- `(u, E)` a relaxed subsolution for `Q` on `U × I` translates to a
relaxed subsolution `(u(· - k), (· + k) '' E)` for `Q(· - k.1)` on `((· + k.1) '' U) × ((· + k.2)
'' I)`. -/
theorem IsParaRelaxedSub.translate {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    {Eset : Set (E d × ℝ)} (h : IsParaRelaxedSub U Q I u Eset) (k : E d × ℝ) :
    IsParaRelaxedSub ((· + k.1) '' U) (fun x ↦ Q (x - k.1)) ((· + k.2) '' I)
      (fun q ↦ u (q - k)) ((fun p ↦ p + k) '' Eset) := by
  obtain ⟨hcont, hnonneg, hclosed, hsub, hpos, hbar⟩ := h
  have hUI : ((· + k.1) '' U) ×ˢ ((· + k.2) '' I) = (fun p : E d × ℝ ↦ p + k) '' (U ×ˢ I) :=
    image_add_prod.symm
  have hmapsTo : ∀ q ∈ ((· + k.1) '' U) ×ˢ ((· + k.2) '' I), q - k ∈ U ×ˢ I := by
    intro q hq
    rw [hUI] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    simpa using hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcont.comp (Continuous.continuousOn (continuous_id.sub continuous_const)) hmapsTo
  · intro p hp; simpa using hnonneg (p - k) (hmapsTo p hp)
  · exact (Homeomorph.addRight k).isClosedMap Eset hclosed
  · have hmono := Set.image_mono (f := fun p : E d × ℝ ↦ p + k) hsub
    rwa [image_add_prod, image_add_closure k.1 U, image_add_closure k.2 I] at hmono
  · rintro p ⟨hpUI, hpos'⟩
    exact ⟨p - k, hpos ⟨hmapsTo p hpUI, hpos'⟩, sub_add_cancel p k⟩
  · intro V a b φ hVab hφ hprec
    have hVab' : AdmissibleCyl U I ((· + (-k).1) '' V) (a + (-k).2) (b + (-k).2) :=
      hVab.translate (-k) (by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := hq
        simpa using hmapsTo p hp)
    set c : E d × ℝ := -k with hc
    have hψ : IsClassicalStrictParaSuper Q (fun q ↦ φ (q - c)) ((· + c.1) '' V) (a + c.2)
        (b + c.2) :=
      hφ.translate c (fun x _ ↦ le_of_eq (by simp [hc, sub_eq_add_neg]))
    have hprec' : PrecOn u (fun q ↦ φ (q - c)) Eset
        (parBdry ((· + c.1) '' V) (a + c.2) (b + c.2)) := by
      rintro p ⟨hpE, hpB⟩
      rw [← image_add_parBdry] at hpB
      obtain ⟨q, hq, rfl⟩ := hpB
      have := hprec q ⟨⟨q + c, hpE, by simp [hc]⟩, hq⟩
      simpa [hc, sub_eq_add_neg] using this
    have hcyl := hbar _ _ _ _ hVab' hψ hprec'
    rintro q ⟨⟨p, hpE, rfl⟩, hq⟩
    have hmem : p ∈ Eset ∩ cyl ((· + c.1) '' V) (a + c.2) (b + c.2) := by
      refine ⟨hpE, ?_⟩
      rw [← image_add_cyl]
      exact ⟨p + k, hq, by simp [hc]⟩
    simpa [hc] using hcyl p hmem

/-- `u` a supersolution for `Q` on `U × I` translates to a supersolution
`u(· - k)` for `Q(· - k.1)` on `((· + k.1) '' U) × ((· + k.2) '' I)`. -/
theorem IsParaSuper.translate {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
    (h : IsParaSuper U Q I u) (k : E d × ℝ) :
    IsParaSuper ((· + k.1) '' U) (fun x ↦ Q (x - k.1)) ((· + k.2) '' I)
      (fun q ↦ u (q - k)) := by
  obtain ⟨hcont, hnonneg, hbar⟩ := h
  have hUI : ((· + k.1) '' U) ×ˢ ((· + k.2) '' I) = (fun p : E d × ℝ ↦ p + k) '' (U ×ˢ I) :=
    image_add_prod.symm
  have hmapsTo : ∀ q ∈ ((· + k.1) '' U) ×ˢ ((· + k.2) '' I), q - k ∈ U ×ˢ I := by
    intro q hq
    rw [hUI] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    simpa using hp
  refine ⟨?_, ?_, ?_⟩
  · exact hcont.comp (Continuous.continuousOn (continuous_id.sub continuous_const)) hmapsTo
  · intro p hp; simpa using hnonneg (p - k) (hmapsTo p hp)
  · intro V a b φ hVab hφ hprec
    have hVab' : AdmissibleCyl U I ((· + (-k).1) '' V) (a + (-k).2) (b + (-k).2) :=
      hVab.translate (-k) (by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := hq
        simpa using hmapsTo p hp)
    set c : E d × ℝ := -k with hc
    have hψ : IsClassicalStrictParaSub Q (fun q ↦ φ (q - c)) ((· + c.1) '' V) (a + c.2)
        (b + c.2) :=
      hφ.translate c (fun x _ ↦ le_of_eq (by simp [hc, sub_eq_add_neg]))
    have hcl := closure_posSetP_univ_comp_sub φ c
    have hprec' : Prec (fun q ↦ φ (q - c)) u univ
        (parBdry ((· + c.1) '' V) (a + c.2) (b + c.2)) := by
      rintro p ⟨hpE, hpB⟩
      rw [← image_add_parBdry] at hpB
      obtain ⟨q, hq, rfl⟩ := hpB
      rw [hcl] at hpE
      obtain ⟨r, hr, hrq⟩ := hpE
      obtain rfl : r = q := by simpa using hrq
      have := hprec r ⟨hr, hq⟩
      simpa [hc, sub_eq_add_neg] using this
    have hcyl := hbar _ _ _ _ hVab' hψ hprec'
    rintro q ⟨hqE, hq⟩
    have hmem : q + c ∈ closure (posSetP (fun q ↦ φ (q - c)) univ) ∩
        cyl ((· + c.1) '' V) (a + c.2) (b + c.2) := by
      refine ⟨?_, ?_⟩
      · rw [hcl]; exact ⟨q, hqE, rfl⟩
      · rw [← image_add_cyl]; exact ⟨q, hq, rfl⟩
    simpa [hc] using hcyl (q + c) hmem

/-! ### Restriction to a smaller domain -/

/-- An admissible cylinder for `U' × I'` is admissible for any larger `U × I`. -/
theorem AdmissibleCyl.mono {U U' : Set (E d)} {I I' : Set ℝ} {V : Set (E d)} {a b : ℝ}
    (h : AdmissibleCyl U' I' V a b) (hU : U' ⊆ U) (hI : I' ⊆ I) : AdmissibleCyl U I V a b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (Set.prod_mono hU hI)⟩

/-- For an admissible cylinder, `∂ₚ(V × (a, b]) ∪ (V × (a, b]) ⊆ V̄ × [a, b] ⊆ U × I`. -/
theorem AdmissibleCyl.parBdry_subset {U : Set (E d)} {I : Set ℝ} {V : Set (E d)} {a b : ℝ}
    (h : AdmissibleCyl U I V a b) : parBdry V a b ⊆ U ×ˢ I := by
  refine Subset.trans ?_ h.2.2.2
  rintro p (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
  · exact ⟨hp1, by rw [mem_singleton_iff.mp hp2]; exact ⟨le_rfl, h.2.2.1.le⟩⟩
  · exact ⟨frontier_subset_closure hp1, hp2⟩

/-- See `AdmissibleCyl.parBdry_subset`. -/
theorem AdmissibleCyl.cyl_subset {U : Set (E d)} {I : Set ℝ} {V : Set (E d)} {a b : ℝ}
    (h : AdmissibleCyl U I V a b) : cyl V a b ⊆ U ×ˢ I :=
  (Set.prod_mono subset_closure Ioc_subset_Icc_self).trans h.2.2.2

/-- Restriction: a supersolution on `U × I` is one on any `U' × I'` with `U' ⊆ U`,
`I' ⊆ I`. -/
theorem IsParaSuper.restrict {U U' : Set (E d)} {Q : E d → ℝ} {I I' : Set ℝ} {u : E d × ℝ → ℝ}
    (h : IsParaSuper U Q I u) (hU : U' ⊆ U) (hI : I' ⊆ I) : IsParaSuper U' Q I' u := by
  obtain ⟨hcont, hnonneg, hbar⟩ := h
  exact ⟨hcont.mono (Set.prod_mono hU hI), fun p hp ↦ hnonneg p (Set.prod_mono hU hI hp),
    fun V a b φ hVab ↦ hbar V a b φ (hVab.mono hU hI)⟩

/-- Restriction: a relaxed subsolution `(u, E)` on `U × I` restricts to the relaxed
subsolution `(u, E ∩ (Ū' × Ī'))` on `U' × I'`, for `U' ⊆ U`, `I' ⊆ I`. -/
theorem IsParaRelaxedSub.restrict {U U' : Set (E d)} {Q : E d → ℝ} {I I' : Set ℝ}
    {u : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)} (h : IsParaRelaxedSub U Q I u Eset)
    (hU : U' ⊆ U) (hI : I' ⊆ I) :
    IsParaRelaxedSub U' Q I' u (Eset ∩ closure U' ×ˢ closure I') := by
  obtain ⟨hcont, hnonneg, hclosed, -, hpos, hbar⟩ := h
  have hUI : U' ×ˢ I' ⊆ U ×ˢ I := Set.prod_mono hU hI
  have hcl : U' ×ˢ I' ⊆ closure U' ×ˢ closure I' := Set.prod_mono subset_closure subset_closure
  refine ⟨hcont.mono hUI, fun p hp ↦ hnonneg p (hUI hp),
    hclosed.inter (isClosed_closure.prod isClosed_closure), inter_subset_right,
    fun p hp ↦ ⟨hpos ⟨hUI hp.1, hp.2⟩, hcl hp.1⟩, ?_⟩
  intro V a b φ hVab hφ hprec
  have hB := hVab.parBdry_subset
  have hC := hVab.cyl_subset
  have := hbar V a b φ (hVab.mono hU hI) hφ
    (fun p hp ↦ hprec p ⟨⟨hp.1, hcl (hB hp.2)⟩, hp.2⟩)
  exact fun p hp ↦ this p ⟨hp.1.1, hp.2⟩

end BernoulliComparison
