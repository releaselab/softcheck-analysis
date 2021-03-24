(lang dune 2.8)

(name softcheck-analysis)

(generate_opam_files true)

(source
 (uri "git+https://github.com/releaselab/softcheck-analysis.git"))

(bug_reports "https://github.com/releaselab/softcheck-analysis/issues")

(homepage "https://github.com/releaselab/softcheck-analysis")

(license MIT)

(authors "Jo\195\163o Santos Reis <joao.reis@ubi.pt>")

(maintainers "Jo\195\163o Santos Reis <joao.reis@ubi.pt>")

(package
 (name softcheck-analysis)
 (synopsis "Example analyses for the Softcheck platform")
 (depends
  (dune :build)
  base
  softcheck
  lattices
  ppx_deriving
  ppx_sexp_conv))
