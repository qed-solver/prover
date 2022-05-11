(use-modules
 (guix packages)
 (guix download)
 (guix git-download)
 (guix utils)
 (guix gexp)
 (guix build-system copy)
 (guix licenses)
 (gnu packages maths))

(define z3-latest
  (package
    (inherit z3)
    (name "z3")
    (version "4.8.17")
    (home-page "https://github.com/Z3Prover/z3")
    (source (origin
              (method git-fetch)
              (uri (git-reference (url home-page)
                                  (commit (string-append "z3-" version))))
              (file-name (git-file-name name version))
              (sha256
               (base32
                "1vvb09q7w7zd29qc4qjysrrhyylszm1wf6azkff004ixwn026b05"))))
    (arguments
     (substitute-keyword-arguments (package-arguments z3)
       ((#:strip-binaries? strip-binaries? #f) '#f)))))

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
 (append (map specification->package
              '("rust-nightly" "rust-analyzer" "clang" "python"))
         (list z3-latest cvc5)))
