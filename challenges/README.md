# Comparator Challenges

This directory contains release comparator workspaces for the public
`BernoulliComparison` API. Each subdirectory is a standalone Lake workspace
with:

- `Challenge.lean`: the trusted statement surface. It imports `Mathlib` only,
  through a few vocabulary files under `Challenge/`; see below.
- `Solution.lean`: the solution proof, importing the library.
- `config.json`: comparator module names, theorem names, and permitted axioms.
- `lakefile.toml`: local workspace metadata, pinned through the parent project.

The `Challenge` files restate all project-local vocabulary inline: the slice
derivatives `dₜ`, `lapₓ`, `gradₓ`, the strict orderings `PrecOn` and `Prec`,
test cylinders and their parabolic boundaries, classical strict barriers, and
the barrier definitions of supersolutions, subsolutions and relaxed
subsolutions of the parabolic Bernoulli problem

    ∂ₜu = Δu in {u > 0},   |∇u| = Q on ∂{u > 0}.

They do not import the library, so a referee can check the meaning of each
statement without reading it. `challenges/comparison/Challenge/Parabolic.lean`
explains the solution notions; read it first.

The inline definitions reuse the library's names, so Comparator also checks
that each one is exactly the library's definition. That check compares the
names of the small auxiliary proofs Lean creates inside definitions, and Lean
shares those proofs only within a file. For this reason the vocabulary is
split into `Challenge/Setting.lean`, `Challenge/Parabolic.lean`, and so on,
following the library's file boundaries (`Interface/Setting.lean`,
`Interface/Parabolic.lean`, …). If a later definition reuses an auxiliary
proof of an earlier one, the earlier definition is restated too, even when no
statement uses it. Every file still imports `Mathlib` only.

## Challenge set

| Directory | Statement certified | Library theorem used by the solution |
|---|---|---|
| `comparison` | Comparison for the parabolic Bernoulli problem on `U × (0, T]`, `U` bounded and open, `Q` Lipschitz on `Ū` with a positive lower bound, `u`, `v` continuous on `Ū × [0, T]`: (a) if `(u, E)` is a relaxed subsolution, `v` a supersolution, and `u < v` on `E` near the parabolic boundary, then `u < v` on `E ∩ (Ū × [0, T])`; (b) the same for a subsolution `u`, with `E = closure {u > 0}` (redundant coverage) | `para_relaxed_comparison`, `para_strict_comparison` |
| `convolution` | Space-time sup-convolution over a compact kernel `K ∋ 0` with spatial radius at most `ℓ` maps a relaxed subsolution for `Q` to a relaxed subsolution for `Q − Lℓ` on the shrunken domain (with the convolved set `E`); inf-convolution maps a supersolution for `Q` to a supersolution for `Q + Lℓ`; `L` is the Lipschitz constant of `Q` | `IsParaRelaxedSub.supConv`, `IsParaSuper.infConv` |
| `heat-bridge` | A relaxed subsolution is a viscosity subsolution of the heat equation in `U × I`, and a supersolution is a viscosity supersolution of the heat equation in its positivity set, both with `C^∞` test functions touching on backward parabolic cylinders (`I` must contain a left neighbourhood of each of its points) | `IsParaRelaxedSub.subcaloric`, `IsParaSuper.supercaloric_on_pos` |
| `model-sanity` | Definition-level sanity checks: explicit strict barriers of both kinds (the supersolution `1 + t − \|x\|²` for `Q ≡ 3`, and the subsolution `1 − \|x\|² − (2d + 1)t` for `Q ≡ 1`, a shrinking ball, up to time `1/(4d + 2)`) with free boundaries meeting the cylinder; positive constants and `(0, ∅)` in the solution classes; and a sign-convention negative test | explicit barriers of the library and the definitions |

### Scope of each challenge

- `comparison` is end-to-end: every hypothesis is a standard assumption or one
  of the two solution notions, stated in the challenge's own vocabulary. The
  solution notions are the barrier (comparison) definitions: a supersolution
  cannot be crossed from below, on any test cylinder `V × (a, b]` with
  `V̄ × [a, b] ⊆ U × I`, by a `C^∞` classical strict subsolution that starts
  below it on the parabolic boundary of the cylinder; symmetrically for
  subsolutions. There are no packaged hypothesis structures.
- The conclusion is strict (`u < v`) and holds only on the ordering set `E`
  (for the standard form, `closure {u > 0}`). Off that set `u ≤ 0 ≤ v` holds in
  `U × (0, T]` by definition. `E = ∅` is allowed but forces `u = 0` in
  `U × (0, T]`, and then the statement is empty; the statement is meaningful
  for every other `E`.
- The strict (standard) form is a short corollary of the relaxed form, so it
  adds little independent coverage.
- `convolution` and `heat-bridge` certify the two main technical inputs of the
  proof. The first-contact analysis that excludes the polar and non-polar
  cases (`Main.core_no_crossing`) has packaged hypotheses (the structure
  `Crossing.Config`), which the headline discharges; it has no challenge of
  its own and is checked for name and axioms only (`formalization.yaml`).
- `model-sanity` is a sanity check and is not counted as coverage of the
  headline results. It guards against the solution notions being vacuous.

## Toolchain

- Lean: `leanprover/lean4:v4.30.0`
- Mathlib: `v4.30.0`
- parabolic-basic-theory (`parabolic_basic_theory`, `v0.1.0`) and its
  dependencies viscosity-solution-theory (`viscosity_solns`) and
  AleksandrovDifferentiability: pinned through the parent
  `lake-manifest.json`. The comparison proof uses the classical solvability
  of the heat Dirichlet problem on ball cylinders from parabolic-basic-theory,
  so a comparator run on these challenges also transitively audits those
  projects.
- Comparator: `leanprover/comparator`, with a `lean4export` build matching Lean
  `v4.30.0` and the pinned `landrun` revision (see
  `scripts/release-comparator.sh`); the release workflow runs on a standard
  GitHub-hosted Linux runner.

Every workspace sets `packagesDir = "../../.lake/packages"` in its
`lakefile.toml` (and records the same folder in its `lake-manifest.json`), so
all of them share the root workspace's dependency checkouts and builds. The
manifests lock the same revisions as the root manifest.

Repository CI builds the full library, validates the manifest against every
challenge configuration and the workspace inventory, and checks headline
declaration names and axioms. On every push it also elaborates the
Challenge/Solution pairs with `scripts/build-challenges.sh --trusted-all`.
That shows each file compiles against the current library; **it does not
compare statements**. Statement equality, proof checking and permitted-axiom
checks for those pairs belong to the separate release Comparator workflow.

Each standalone workspace defaults to its `Challenge` target only, so a plain
`lake build` is safe while preparing an adversarial Comparator run: it does
not prebuild `Solution.lean`.

## Acceptance

For routine development in a trusted checkout:

```sh
lake exe cache get && lake build
./scripts/build-challenges.sh --trusted-all
```

For a Comparator release run, dispatch `.github/workflows/release-comparator.yml`
on a fresh release-candidate commit. It installs the pinned tools, runs every
configuration, and uploads an attestation artifact. Treat `Solution.lean` as
potentially adversarial. Review and trust the release checkout's
`Challenge.lean` and `Challenge/*.lean`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `config.json`, and the Comparator toolchain. Then:

1. Run `make challenges-challenge-only` (or `lake build` in an individual
   workspace). This elaborates only the trusted `Challenge` target.
2. Invoke Comparator in its release sandbox with that workspace's
   `config.json`, without first running `lake build Solution` or the trusted
   all-workspace driver.
3. Confirm that each theorem depends only on `propext`, `Classical.choice`
   and `Quot.sound`.

### Recorded acceptance

The release Comparator workflow accepted all four workspaces on 2026-09-27,
on a standard GitHub-hosted Linux runner, with Lean `v4.30.0`, Mathlib
`c5ea003`, Comparator `d03acab`, `landrun` `5ed4a3d`, and `lean4export`
`a3e35a5`, on a release candidate with the same Lean sources as this
release:

| Workspace | Statement comparison and kernel check | Axioms |
|---|---|---|
| `comparison` | PASS | `propext`, `Classical.choice`, `Quot.sound` only |
| `convolution` | PASS | same |
| `heat-bridge` | PASS | same |
| `model-sanity` | PASS | same |

The GitHub release carries the attestation artifact from running this
workflow on the release commit itself: commit and tree hashes, toolchain and
tool revisions, per-workspace results, and complete logs. Comparator ran under
`landrun` without the additional `systemd-run` containment that upstream
recommends for a full adversarial guarantee.

As a local, non-sandboxed pre-check, `scripts/check-challenge-definitions.lean`
compares every definition restated in a workspace's `Challenge` modules,
including auxiliary proofs, against the library constant of the same name
(kind, type, value, universe parameters, reducibility hints). It does not
replace Comparator. Usage, from inside a workspace after
`lake build Challenge Solution`:

```sh
lake env lean --run ../../scripts/check-challenge-definitions.lean <theorem names from config.json>
```
