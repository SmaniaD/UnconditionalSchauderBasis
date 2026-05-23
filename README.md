# UnconditionalSchauderBasis

A Lean 4/mathlib project formalizing Schauder bases, unconditional Schauder
bases, and a finite sign criterion for constructing unconditional Schauder
bases in complete normed spaces.

[Doc-Gen documentation](https://smaniad.github.io/UnconditionalSchauderBasis/UnconditionalSchauderBasis.html)

## Current State

The main Lean source file is `UnconditionalSchauderBasis.lean`. It currently
contains:

- `HasSchauderSum`: ordered convergence of initial partial sums.
- `SchauderBasis`: a bundled `ℕ`-indexed Schauder basis with continuous
  coordinate maps and unique ordered coordinate expansions.
- `UnconditionalSchauderBasis`: a Schauder basis whose coordinate expansion is
  unconditionally summable.
- `UnconditionalSchauderBasisAbstractIndex`: an arbitrary-index version using
  `HasSum`, the finite-set filter for unconditional summability.
- Conversion lemmas between the abstract-index API and the usual `ℕ`-indexed
  API when an enumeration is available.
- `UnconditionalCriterion.HasDenseSpan` and
  `UnconditionalCriterion.HasFiniteSignBound`, the hypotheses for the finite
  sign criterion.
- Completed existence theorems:
  `UnconditionalCriterion.exists_unconditionalSchauderBasisAbstractIndex_of_finiteSignBound`
  and
  `UnconditionalCriterion.exists_unconditionalSchauderBasis_of_finiteSignBound`.

The finite sign criterion first constructs an abstractly indexed unconditional
Schauder basis. The sequence-indexed theorem is then obtained by specializing
the index type to `ℕ`.

## Build

This project uses the Lean toolchain pinned in `lean-toolchain`, currently
`leanprover/lean4:v4.30.0-rc2`, and mathlib through Lake.

```sh
lake build
```

For a quick check of the main file:

```sh
lake env lean UnconditionalSchauderBasis.lean
```

## Project Files

- `lakefile.toml`: Lake package configuration.
- `lean-toolchain`: Lean toolchain pin.
- `lake-manifest.json`: resolved dependency manifest.
- `UnconditionalSchauderBasis.lean`: main formalization file and library entry
  point.

## Next Work

Likely next steps are:

- split the finite sign criterion into topic-focused files if the file grows
  further;
- add examples or small downstream theorems using the constructed
  unconditional Schauder basis;
- expand the API around coordinate projections and rearrangements as needed by
  future applications.
