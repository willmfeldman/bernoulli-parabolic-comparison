/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Crossing.Instance
public import BernoulliComparison.NonPolar.Exclusion
public import BernoulliComparison.Polar.Exclusion

/-!
# Core no-crossing

In the convolved configuration (`Crossing.Config`), with `d ≥ 1`, the convolved pair is strictly
ordered on the convolved set: `u₁ < v₁` on `E₁`.

The proof is by contradiction, assembled from:

1. `Crossing.Config.crossingSet`: the crossing set `S = {p ∈ E₁ | v₁ p ≤ u₁ p}`; if
   `u₁ < v₁` fails somewhere on `E₁`, then `S ≠ ∅`;
2. `Contact.exists_contactData`: from `S ≠ ∅` (via the first crossing time), a contact point
   `p⋆` with touching-ball data, including the unit normals `ν¹`, `ν²` of the interior and
   exterior space-time balls at `p⋆` (`Contact/Data.lean`);
3. `NonPolar.no_nonpolar`: `ν¹ₓ = 0 ∨ ν²ₓ = 0`, i.e. the contact is not doubly non-polar;
4. `Polar.no_polar` (from `south_reduction`, `no_north_interior`, `no_north_exterior`):
   `ν¹ₓ ≠ 0 ∧ ν²ₓ ≠ 0`, i.e. neither normal is polar (purely in the time direction).

Steps 3 and 4 contradict each other. Hence `S = ∅`, which is the statement.
-/

@[expose] public section

open Set

namespace BernoulliComparison

namespace Main

open Crossing

variable {d : ℕ}

/-- **Core no-crossing.** In the configuration `P` (the convolved δ-scaled pair
`u₁ = û^K`, `v₁ = v̂_K`, `E₁ = D₁ ∩ (E ⊖ K)`), for `d ≥ 1` and `D_{ρ₀} ≠ ∅`: `u₁ < v₁` on `E₁`.

The condition `ρ₀ ≤ T` is the field `P.ρ₀_le`. The proof is outlined in the module docstring;
the hypothesis `_hne` (`D_{ρ₀} ≠ ∅`) is not used. -/
theorem core_no_crossing (hd : 1 ≤ d) {U : Set (E d)} {Q : E d → ℝ} {T : ℝ}
    {u v : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)} (P : Config U Q T u v Eset)
    (_hne : (interiorRegion U T P.ρ₀).Nonempty) :
    ∀ p ∈ P.E₁, P.u₁ p < P.v₁ p := by
  intro p hp
  by_contra hlt
  have hS : P.crossingSet.Nonempty := ⟨p, hp, not_lt.1 hlt⟩
  obtain ⟨C⟩ := Contact.exists_contactData hd P hS
  obtain ⟨h₁, h₂⟩ := Polar.no_polar C
  rcases NonPolar.no_nonpolar hd C with h | h
  · exact h₁ h
  · exact h₂ h

end Main

end BernoulliComparison
