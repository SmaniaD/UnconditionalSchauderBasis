MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen
lake build UnconditionalSchauderBasis:docs
rm -rf ../docs
mkdir ../docs
cp -r .lake/build/doc/. ../docs/
cd ../docs/
git add docs
if git diff --cached --quiet; then
  echo "No documentation changes to commit."
else
  git commit -m "Update generated documentation"
  git push
fi
python3 -m http.server



