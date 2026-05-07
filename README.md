# UnconditionalSchauderBasis

A Lean 4/mathlib project formalizing Schauder bases and unconditional
Schauder bases for Banach spaces.

## Current State

The project currently contains:

- `SchauderBasis`: a bundled Schauder basis with basis vectors, continuous
  coordinate functionals, representation by a convergent series, and uniqueness
  of coefficients.
- `UnconditionalSchauderBasis`: a Schauder basis together with unconditional
  convergence of all rearranged basis expansions.
- `UnconditionalCriterion`: definitions and lemmas for constructing an
  unconditional Schauder basis from finite sign estimates.
- A completed Lean proof pipeline from the finite sign bound to the existence
  of an unconditional Schauder basis, exposed as
  `UnconditionalCriterion.exists_unconditionalSchauderBasis_of_finiteSignBound`.

There are two Lean files at the moment:

- `UnconditionalSchauderBasis.lean`: the library entry point built by Lake.
- `UnconditionalSchauderBasis/UnconditionalSchauderBasisNontrivialField.lean`:
  a version generalized over a nontrivially normed field of characteristic zero.

## Build

This project uses Lean `v4.30.0-rc2` and mathlib through Lake.

```sh
lake build
```

As of this README, `lake build` completes successfully. The build emits a few
unused section-variable linter warnings, but no errors.

## Project Files

- `lakefile.toml`: Lake package configuration.
- `lean-toolchain`: Lean toolchain pin.
- `lake-manifest.json`: resolved dependency manifest.
- `UnconditionalSchauderBasis.lean`: main formalization file.

## Next Work

Likely next steps are:

- decide whether the generalized nontrivially normed field version should
  replace or be imported by the top-level library entry point;
- clean up the unused section-variable warnings;
- add examples or small downstream theorems using the constructed
  unconditional Schauder basis.
