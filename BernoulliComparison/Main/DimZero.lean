/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Touching.PastPoints
public import BernoulliComparison.Crossing.Abstract

/-!
# The main theorem in dimension zero

In `E 0 = ℝ⁰` every set is `∅` or `univ`, gradients and Laplacians vanish, and the only
admissible cylinders of `univ × (0, T]` are `univ × (a, b]` with `0 < a < b ≤ T`, with parabolic
boundary `univ × {a}`. The contact analysis used for `d ≥ 1` does not apply; instead the proof
works directly from the barrier definitions (`IsParaRelaxedSub`, `IsParaSuper`), with time-affine
test functions:

* Step 1 (`dimZero_sub_le`): `u` does not increase along `E`;
* Step 2 (`dimZero_super_le`): `v` does not decrease from a time where it is positive;
* Step 3 (`para_relaxed_comparison_dim_zero`): the first time of `{v ≤ u} ∩ E` is positive (the
  order holds near `∂ₚ = univ × {0}`), it has a strictly earlier point of `E` at positive time
  (`IsParaRelaxedSub.past_points_euclidean`, valid for `d = 0`), and Steps 1–2 contradict the
  crossing there.

`precOn_of_eq_empty` is the (dimension-free) empty-domain case.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

namespace BernoulliComparison

namespace Main

variable {d : ℕ}

/-- The empty-domain case. If `U = ∅` then `E ⊆ Ū × [0, T] = ∅` and every
ordering on `E` holds. -/
theorem precOn_of_eq_empty {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
    {Eset F : Set (E d × ℝ)} (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hU : U = ∅) :
    PrecOn u v Eset F := by
  rintro p ⟨hpE, -⟩
  have := (hsub.2.2.2.1 hpE).1
  simp [hU] at this

/-! ### Calculus on `ℝ⁰` -/

/-- In `E 0` the spatial Laplacian vanishes: every time slice is constant. -/
theorem lapₓ_dim_zero (φ : E 0 × ℝ → ℝ) (p : E 0 × ℝ) : lapₓ φ p = 0 := by
  have h : (fun y : E 0 ↦ φ (y, p.2)) = fun _ ↦ φ (p.1, p.2) :=
    funext fun y ↦ by rw [Subsingleton.elim y p.1]
  simp [lapₓ, h]

/-- In `E 0` the spatial gradient vanishes (`E 0` is a subsingleton). -/
theorem gradₓ_dim_zero (φ : E 0 × ℝ → ℝ) (p : E 0 × ℝ) : gradₓ φ p = 0 :=
  Subsingleton.elim _ _

/-- The time derivative of a time-affine function. -/
theorem dₜ_affine {d : ℕ} (c η a : ℝ) (p : E d × ℝ) :
    dₜ (fun q : E d × ℝ ↦ c + η * (q.2 - a)) p = η := by
  have h : HasDerivAt (fun s : ℝ ↦ c + η * (s - a)) η p.2 := by
    simpa using (((hasDerivAt_id p.2).sub_const a).const_mul η).const_add c
  exact h.deriv

theorem contDiff_affine {d : ℕ} (c η a : ℝ) :
    ContDiff ℝ ∞ (fun q : E d × ℝ ↦ c + η * (q.2 - a)) :=
  contDiff_const.add (contDiff_const.mul (contDiff_snd.sub contDiff_const))

/-- A nonempty subset of `E 0` is `univ`. -/
theorem eq_univ_of_nonempty_dim_zero {U : Set (E 0)} (hU : U.Nonempty) : U = univ :=
  Subsingleton.eq_univ_of_nonempty hU

theorem isBounded_univ_dim_zero : Bornology.IsBounded (univ : Set (E 0)) :=
  Set.subsingleton_univ.finite.isBounded

/-- The admissible cylinders of `univ × (0, T]` in `E 0`. -/
theorem admissibleCyl_univ_dim_zero {T a b : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b ≤ T) :
    AdmissibleCyl (univ : Set (E 0)) (Ioc 0 T) univ a b :=
  ⟨isOpen_univ, isBounded_univ_dim_zero, hab, fun _ hp ↦
    ⟨mem_univ _, ha.trans_le hp.2.1, hp.2.2.trans hbT⟩⟩

/-- In `E 0`, `∂ₚ(univ × (a, b]) = univ × {a}`. -/
theorem snd_eq_of_mem_parBdry_univ {a b : ℝ} {p : E 0 × ℝ} (hp : p ∈ parBdry univ a b) :
    p.2 = a := by
  rcases hp with hp | hp
  · exact hp.2
  · simp at hp

/-! ### Step 1: `u` does not increase along `E` -/

/-- Dimension zero, Step 1. For a relaxed subsolution `(u, E)` on `ℝ⁰ × (0, T]`
(with `U = univ` and `Q > 0`), `u(t) ≤ u(a)` whenever `0 < a < t ≤ T` and `(x, t) ∈ E`. Test
function: `φ = u(a) + ε/2 + ε/(2(t - a)) · (s - a)`, a strict supersolution
(`∂ₜφ > 0`, `∇φ = 0`). -/
theorem dimZero_sub_le {Q : E 0 → ℝ} {T : ℝ} {u : E 0 × ℝ → ℝ} {Eset : Set (E 0 × ℝ)}
    (hsub : IsParaRelaxedSub univ Q (Ioc 0 T) u Eset) (hQ : ∀ x, 0 < Q x) {x : E 0}
    {a t : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ T) (hp : (x, t) ∈ Eset) :
    u (x, t) ≤ u (x, a) := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have hta : 0 < t - a := sub_pos.2 hat
  set η := ε / (2 * (t - a)) with hη
  have hηpos : 0 < η := by positivity
  set φ : E 0 × ℝ → ℝ := fun q ↦ (u (x, a) + ε / 2) + η * (q.2 - a) with hφ
  have hsuper : IsClassicalStrictParaSuper Q φ univ a t := by
    refine ⟨contDiff_affine _ _ _, fun p _ ↦ ?_, fun p _ ↦ ?_⟩
    · rw [hφ, dₜ_affine, lapₓ_dim_zero]; linarith
    · rw [gradₓ_dim_zero, norm_zero]; exact hQ _
  have hbd : PrecOn u φ Eset (parBdry univ a t) := by
    rintro p ⟨-, hp⟩
    have h2 := snd_eq_of_mem_parBdry_univ hp
    have hpx : p = (x, a) := Prod.ext (Subsingleton.elim _ _) h2
    subst hpx
    simp only [hφ, sub_self, mul_zero, add_zero]
    linarith
  have := hsub.2.2.2.2.2 univ a t φ (admissibleCyl_univ_dim_zero ha hat htT) hsuper hbd (x, t)
    ⟨hp, mem_univ _, hat, le_rfl⟩
  have hφt : φ (x, t) = u (x, a) + ε := by
    simp only [hφ, hη]; field_simp; ring
  linarith

/-! ### Step 2: `v` does not decrease where positive -/

/-- Dimension zero, Step 2. For a supersolution `v` on `ℝ⁰ × (0, T]` (with `U = univ`),
`v(a) ≤ v(t)` whenever `0 < a < t ≤ T` and `v(x, a) > 0`. Test function:
`φ = v(a) - ε' - ε'/(t - a) · (s - a)`, positive on `[a, t]`, a strict subsolution
(`∂ₜφ < 0`, and `∂{φ > 0}` does not meet `univ × [a, t]`). -/
theorem dimZero_super_le {Q : E 0 → ℝ} {T : ℝ} {v : E 0 × ℝ → ℝ}
    (hsuper : IsParaSuper univ Q (Ioc 0 T) v) {x : E 0} {a t : ℝ} (ha : 0 < a) (hat : a < t)
    (htT : t ≤ T) (hva : 0 < v (x, a)) : v (x, a) ≤ v (x, t) := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have hta : 0 < t - a := sub_pos.2 hat
  set ε' := min (ε / 2) (v (x, a) / 4) with hε'
  have hε'pos : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'1 : ε' ≤ ε / 2 := min_le_left _ _
  have hε'2 : ε' ≤ v (x, a) / 4 := min_le_right _ _
  set η := ε' / (t - a) with hη
  have hηpos : 0 < η := by positivity
  set φ : E 0 × ℝ → ℝ := fun q ↦ (v (x, a) - ε') + (-η) * (q.2 - a) with hφ
  have hφcont : Continuous φ := (contDiff_affine (d := 0) _ _ _).continuous
  -- `φ ≥ v(a) - 2ε' > 0` on `[a, t]`
  have hφpos : ∀ q : E 0 × ℝ, q.2 ∈ Icc a t → 0 < φ q := by
    intro q hq
    have h1 : η * (q.2 - a) ≤ ε' := by
      calc η * (q.2 - a) ≤ η * (t - a) := by
            exact mul_le_mul_of_nonneg_left (by linarith [hq.2]) hηpos.le
        _ = ε' := by rw [hη]; field_simp
    simp only [hφ]
    linarith
  have hsubφ : IsClassicalStrictParaSub Q φ univ a t := by
    refine ⟨contDiff_affine _ _ _, fun p _ ↦ ?_, fun p hp ↦ ?_⟩
    · rw [hφ, dₜ_affine, lapₓ_dim_zero]; linarith
    · exfalso
      have hpos : p ∈ {q | 0 < φ q} := hφpos p hp.2.2
      have hopen : IsOpen {q | 0 < φ q} := isOpen_lt continuous_const hφcont
      exact hp.1.2 (hopen.interior_eq.symm ▸ hpos)
  have hbd : Prec φ v univ (parBdry univ a t) := by
    rintro p ⟨-, hp⟩
    have h2 := snd_eq_of_mem_parBdry_univ hp
    have hpx : p = (x, a) := Prod.ext (Subsingleton.elim _ _) h2
    subst hpx
    simp only [hφ, sub_self, mul_zero, add_zero]
    linarith
  have hmem : (x, t) ∈ closure (posSetP φ univ) :=
    subset_closure ⟨mem_univ _, hφpos _ ⟨hat.le, le_rfl⟩⟩
  have := hsuper.2.2 univ a t φ (admissibleCyl_univ_dim_zero ha hat htT) hsubφ hbd (x, t)
    ⟨hmem, mem_univ _, hat, le_rfl⟩
  have hφt : φ (x, t) = v (x, a) - 2 * ε' := by
    simp only [hφ, hη]; field_simp; ring
  linarith

/-! ### Step 3: the main theorem for `d = 0` -/

/-- **The comparison principle for `d = 0`.** Same hypotheses and conclusion as
`para_relaxed_comparison` with `d = 0`. -/
theorem para_relaxed_comparison_dim_zero {U : Set (E 0)} {Q : E 0 → ℝ} {T : ℝ}
    {u v : E 0 × ℝ → ℝ} {Eset N : Set (E 0 × ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaRelaxedSub U Q (Ioc 0 T) u Eset) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    (hN : N ∈ 𝓝ˢ (parBdry U 0 T)) (hprec : PrecOn u v Eset N) :
    PrecOn u v Eset (closure U ×ˢ Icc 0 T) := by
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · exact precOn_of_eq_empty hsub hU0
  have hUu : U = univ := eq_univ_of_nonempty_dim_zero hUne
  subst hUu
  rw [closure_univ] at hQ hQpos hu hv ⊢
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨c, hc, hcQ⟩ := hQpos
  have hQ0 : ∀ x, 0 < Q x := fun x ↦ hc.trans_le (hcQ x (mem_univ _))
  have hQc : ∀ x, ContinuousAt Q x := fun x ↦
    hK.continuousOn.continuousAt (univ_mem' fun _ ↦ mem_univ _)
  have hED : Eset ⊆ univ ×ˢ Icc 0 T := by
    have := hsub.2.2.2.1
    rwa [closure_univ, closure_Ioc hT.ne] at this
  -- The past-points property in the form: a point of `E` at a positive time has points of `E`
  -- at earlier times within any distance `ε`.
  have hpast : ∀ p ∈ Eset, 0 < p.2 → ∀ ε > 0, ∃ q ∈ Eset, q.2 < p.2 ∧ p.2 - ε < q.2 := by
    intro p hpE hp0 ε hε
    have hpI : p.2 ∈ Ioc 0 T := ⟨hp0, (hED hpE).2.2⟩
    obtain ⟨q, hqE, hqt, hq⟩ := hsub.past_points_euclidean isOpen_univ (mem_univ _)
      (Ioc_mem_nhdsLE_of_mem hpI) (hQc _) (hQ0 _) hpE hε
    refine ⟨q, hqE, hqt, ?_⟩
    have h2 : (q.2 - p.2) ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg ‖q.1 - p.1‖]
    have := abs_lt_of_sq_lt_sq h2 hε.le
    linarith [(abs_lt.1 this).1]
  have hTS : ∀ p ∈ Eset ∩ {p : E 0 × ℝ | 0 < p.2},
      p ∈ closure (Eset ∩ {q : E 0 × ℝ | q.2 < p.2}) := by
    rintro p ⟨hpE, hp0⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hqE, hqt, hq⟩ := hpast p hpE hp0 ε hε
    refine ⟨q, ⟨hqE, hqt⟩, ?_⟩
    rw [Prod.dist_eq, Subsingleton.elim p.1 q.1, dist_self, Real.dist_eq,
      abs_of_pos (by linarith)]
    exact max_lt hε (by linarith)
  have hgap : ∀ p ∈ Eset \ {p : E 0 × ℝ | 0 < p.2}, u p < v p := by
    rintro p ⟨hpE, hp0⟩
    have hpD := hED hpE
    have hp2 : p.2 = 0 := le_antisymm (not_lt.1 hp0) hpD.2.1
    have hpB : p ∈ parBdry univ 0 T := Or.inl ⟨by rw [closure_univ]; exact mem_univ _, hp2⟩
    exact hprec p ⟨hpE, subset_of_mem_nhdsSet hN hpB⟩
  by_contra hcon
  have hne : {p ∈ Eset | v p ≤ u p}.Nonempty := by
    simp only [PrecOn, not_forall, not_lt] at hcon
    obtain ⟨p, ⟨hpE, -⟩, hle⟩ := hcon
    exact ⟨p, hpE, hle⟩
  obtain ⟨p₀, ⟨hp₀E, hp₀le⟩, -, hbefore, -, -, -, -, hSR⟩ :=
    Crossing.first_crossing ((isCompact_univ (X := E 0)).prod isCompact_Icc)
      hsub.2.2.1 hED hu hv hgap hTS hne
  have hp₀pos : 0 < p₀.2 := hSR ⟨hp₀E, hp₀le⟩
  have hp₀T : p₀.2 ≤ T := (hED hp₀E).2.2
  -- a point of `E` at a positive time before `t⋆ = p₀.2`
  obtain ⟨q, hqE, hqt, hq0⟩ := hpast p₀ hp₀E hp₀pos p₀.2 hp₀pos
  rw [sub_self] at hq0
  have huv : u q < v q := hbefore q hqE hqt
  have hqT : q.2 ≤ T := (hED hqE).2.2
  have huq : 0 ≤ u q := hsub.2.1 q ⟨mem_univ _, hq0, hqT⟩
  have hq : q = (q.1, q.2) := rfl
  have hp₀ : p₀ = (q.1, p₀.2) := Prod.ext (Subsingleton.elim _ _) rfl
  have hv₁ : v q ≤ v p₀ := by
    rw [hq, hp₀]
    exact dimZero_super_le hsuper hq0 hqt hp₀T (by rw [← hq]; linarith)
  have hu₁ : u p₀ ≤ u q := by
    rw [hq, hp₀]
    exact dimZero_sub_le hsub hQ0 hq0 hqt hp₀T (hp₀ ▸ hp₀E)
  linarith

end Main

end BernoulliComparison
