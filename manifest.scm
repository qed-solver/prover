(use-modules
 (guix packages)
 (guix download)
 (guix git-download)
 (guix utils)
 (guix gexp)
 (guix build-system copy)
 (guix licenses)
 (gnu packages maths))

(define license (@ (guix licenses) license))

(define cvc5
  (package
   (name "cvc5")
   (version "1.0.0")
   (source (origin
            (method url-fetch)
            (uri (string-append "https://github.com/cvc5/cvc5/releases/download/cvc5-" version "/cvc5-Linux"))
            (file-name (string-append name "-Linux"))
            (sha256 "0192llkzah60b3phprp0zq1m4ly8w1sgp2yqp4r5iwxy88n05c77")))
   (build-system copy-build-system)
   (arguments
    `(#:install-plan `(("cvc5-Linux" "bin/cvc5"))
      #:strip-binaries? #f
      #:phases
      (modify-phases %standard-phases
        (add-before 'install 'chmod
          (lambda* (#:key inputs outputs #:allow-other-keys)
            (chmod "cvc5-Linux" #o755))))))
   (synopsis "Automatic theorem prover for Satisfiability Modulo Theories (SMT) problems")
   (description "cvc5 is a tool for determining the satisfiability of a first order formula modulo a first order theory (or a combination of such theories). It is the fifth in the Cooperating Validity Checker family of tools (CVC, CVC Lite, CVC3, CVC4) but does not directly incorporate code from any previous version prior to CVC4.")
   (license (license "cvc5" "https://github.com/cvc5/cvc5/blob/main/COPYING" #f))
   (home-page "https://cvc5.github.io/")))

(packages->manifest
 (cons* cvc5
        (map specification->package
              '("z3" "rust-nightly" "rust-analyzer" "clang" "python"))))
