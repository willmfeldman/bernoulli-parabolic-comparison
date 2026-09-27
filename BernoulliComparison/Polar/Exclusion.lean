/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BernoulliComparison.Polar.SouthReduction
public import BernoulliComparison.Polar.NorthExterior

/-!
# No polar contacts

At a contact point neither normal is polar: `ν¹ₓ ≠ 0` and `ν²ₓ ≠ 0` (`no_polar`). A polar unit
normal is `±e_t`; the north poles are excluded by `no_north_interior` and `no_north_exterior`, and
the south poles are reduced to the north pole of the other normal by `south_reduction`.

The polar arguments use the raw pair `(û, E)` and the raw supersolution `v̂` near a point of the
rim of the spatial disk `B̄_{λ₁}(x⋆)` (unwinding of the first convolution, `Polar/Unwind.lean`),
one domain comparison against an explicit self-similar barrier (`Barriers/PolarRadial.lean`), and
a static slope lemma (`Barriers/Slope.lean`). They use only `c₁ > 0` and `c₂ > 0`, not the gap
`c₂ < c₁`, and they use `λ₁ > 0`.

This differs from Kim (2003), Lemma 2.3 ("`H` is not horizontal"), which replaces the
convolution balls by ellipsoids, rescales `u` parabolically at the contact point and compares it
with an explicit radial barrier, and treats the supersolution side only by a parallel argument.
Here each of the two north poles has its own proof, and each is excluded by a single comparison
at the rim of the spatial disk.

## Reference

* I. C. Kim, *A free boundary problem arising in flame propagation*, J. Differential Equations
  191 (2003), 470–489.
-/

@[expose] public section

namespace BernoulliComparison

namespace Polar

open Crossing Config Contact

variable {d : ℕ}

/-- A Euclidean unit vector with vanishing spatial part is `e_t` or `-e_t`. -/
theorem eq_et_or_eq_neg_et {ν : E d × ℝ} (hν : ‖ν.1‖ ^ 2 + ν.2 ^ 2 = 1) (h : ν.1 = 0) :
    ν = ((0 : E d), (1 : ℝ)) ∨ ν = ((0 : E d), (-1 : ℝ)) := by
  rw [h, norm_zero] at hν
  have h2 : (ν.2 - 1) * (ν.2 + 1) = 0 := by linear_combination hν
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl (Prod.ext h (by simp; linarith))
  · exact Or.inr (Prod.ext h (by simp; linarith))

variable {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)} {P : Config U Q T u v Eset}

/-- No polar contact: at a contact point neither normal is polar,
`ν¹ₓ ≠ 0` and `ν²ₓ ≠ 0`. -/
theorem no_polar (C : ContactData P) : C.ν₁.1 ≠ 0 ∧ C.ν₂.1 ≠ 0 := by
  constructor
  · intro h
    rcases eq_et_or_eq_neg_et C.ν₁_unit h with h1 | h1
    · exact no_north_interior C h1
    · exact no_north_exterior C ((south_reduction C).2 h1)
  · intro h
    rcases eq_et_or_eq_neg_et C.ν₂_unit h with h2 | h2
    · exact no_north_exterior C h2
    · exact no_north_interior C ((south_reduction C).1 h2)

end Polar

end BernoulliComparison
