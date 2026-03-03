dune build @doc
git checkout gh-pages
rsync -av _build/default/_doc/_html/ ./docs/