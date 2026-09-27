import BernoulliComparison

/-!
# Solution: sup- and inf-convolution preserve the solution classes

Assembles the library's convolution-step structure `ConvStep` from the individual hypotheses and
applies `IsParaRelaxedSub.supConv` and `IsParaSuper.infConv`
(`BernoulliComparison/Convolution/Preservation.lean`).
-/

open Set Filter Topology

namespace BernoulliComparison

variable {d : ℕ}

theorem challenge_supConv {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}
    {Q : E d → ℝ} {u : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)} {L : NNReal} {ℓ : ℝ}
    (hu : IsParaRelaxedSub U Q (Ioc α β) u Eset) (hcont : ContinuousOn u (closure U ×ˢ Icc α β))
    (hU : Bornology.IsBounded U) (hαβ : α < β) (hαβ' : α' < β') (hK : IsCompact K)
    (h0K : (0 : E d × ℝ) ∈ K) (hKℓ : ∀ k ∈ K, ‖k.1‖ ≤ ℓ)
    (hclosed : ∀ p ∈ closure U' ×ˢ Icc α' β', ∀ k ∈ K, p + k ∈ closure U ×ˢ Icc α β)
    (hopen : ∀ p ∈ U' ×ˢ Ioc α' β', ∀ k ∈ K, p + k ∈ U ×ˢ Ioc α β)
    (hQ : LipschitzOnWith L Q (closure U)) :
    IsParaRelaxedSub U' (fun x ↦ Q x - L * ℓ) (Ioc α' β') (supConv K u)
      (setConv (closure U' ×ˢ Icc α' β') K Eset) :=
  hu.supConv hcont ⟨hU, hαβ, hαβ', hK, ⟨0, h0K⟩, hclosed, hopen⟩ h0K hKℓ hQ

theorem challenge_infConv {U U' : Set (E d)} {α β α' β' : ℝ} {K : Set (E d × ℝ)}
    {Q : E d → ℝ} {v : E d × ℝ → ℝ} {L : NNReal} {ℓ : ℝ}
    (hv : IsParaSuper U Q (Ioc α β) v) (hcont : ContinuousOn v (closure U ×ˢ Icc α β))
    (hU : Bornology.IsBounded U) (hαβ : α < β) (hαβ' : α' < β') (hK : IsCompact K)
    (h0K : (0 : E d × ℝ) ∈ K) (hKℓ : ∀ k ∈ K, ‖k.1‖ ≤ ℓ)
    (hclosed : ∀ p ∈ closure U' ×ˢ Icc α' β', ∀ k ∈ K, p + k ∈ closure U ×ˢ Icc α β)
    (hopen : ∀ p ∈ U' ×ˢ Ioc α' β', ∀ k ∈ K, p + k ∈ U ×ˢ Ioc α β)
    (hQ : LipschitzOnWith L Q (closure U)) :
    IsParaSuper U' (fun x ↦ Q x + L * ℓ) (Ioc α' β') (infConv K v) :=
  hv.infConv hcont ⟨hU, hαβ, hαβ', hK, ⟨0, h0K⟩, hclosed, hopen⟩ h0K hKℓ hQ

end BernoulliComparison
