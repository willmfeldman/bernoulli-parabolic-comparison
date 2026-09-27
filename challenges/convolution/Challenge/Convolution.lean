import Challenge.Setting

/-!
# Challenge vocabulary: sup- and inf-convolutions over a kernel

Part of the trusted statement surface; imports `Mathlib` only (through `Challenge.Setting`).
Restates, token for token, definitions of the library file
`BernoulliComparison/Convolution/Basic.lean`.

For a set `K ⊆ ℝᵈ × ℝ` (the kernel; compact and nonempty in the challenge) and
`w : ℝᵈ × ℝ → ℝ`:

* `supConv K w p = sup_{k ∈ K} w (p + k)` and `infConv K w p = inf_{k ∈ K} w (p + k)`
  (Mathlib's conditionally complete `sSup`/`sInf` of the image of `K`);
* `reachSet K E = {p | ∃ k ∈ K, p + k ∈ E}` (the set `E - K`);
* `setConv D' K E = D' ∩ reachSet K E`, the convolved set restricted to the target box `D'`.
-/

open Set Filter Topology Pointwise

namespace BernoulliComparison

variable {d : ℕ}

/-- The sup-convolution `w^K(p) = sup_{k ∈ K} w (p + k)`. -/
noncomputable def supConv (K : Set (E d × ℝ)) (w : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  sSup ((fun k ↦ w (p + k)) '' K)

/-- The inf-convolution `w_K(p) = inf_{k ∈ K} w (p + k)`. -/
noncomputable def infConv (K : Set (E d × ℝ)) (w : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  sInf ((fun k ↦ w (p + k)) '' K)

/-- The points `p` whose translate `p + K` meets `Eset`, i.e. `Eset - K`. -/
def reachSet (K Eset : Set (E d × ℝ)) : Set (E d × ℝ) :=
  {p | ∃ k ∈ K, p + k ∈ Eset}

/-- The convolved set `D' ∩ (Eset - K)`, for the target box `D'`. -/
def setConv (D' K Eset : Set (E d × ℝ)) : Set (E d × ℝ) :=
  D' ∩ reachSet K Eset

end BernoulliComparison
