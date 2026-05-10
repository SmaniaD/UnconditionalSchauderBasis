#!/bin/bash
set -e

# raiz do repositório Lean
LEAN_ROOT="$(pwd)"

MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen
lake build UnconditionalSchauderBasis:docs

# raiz git
REPO_ROOT="$(git rev-parse --show-toplevel)"

rm -rf "$REPO_ROOT/docs"
mkdir -p "$REPO_ROOT/docs"
cp -r "$LEAN_ROOT/.lake/build/doc/." "$REPO_ROOT/docs/"

cd "$REPO_ROOT"

git status --short docs

git add -A docs

if git diff --cached --quiet; then
  echo "No documentation changes to commit."
else
  git commit -m "Update generated documentation"
  git push
fi

cd docs
python3 -m http.server



