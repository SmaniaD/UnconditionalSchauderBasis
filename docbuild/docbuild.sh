MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen
lake build UnconditionalSchauderBasis:docs
rm -rf ../docs
mkdir ../docs
cp -r .lake/build/doc/. ../docs/
cd  ..
git add docs
git commit -m "Update generated documentation"
git push
cd docs
python3 -m http.server



