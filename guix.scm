;;; SPDX-License-Identifier: PMPL-1.0-or-later
;;; Guix package definition for Eclexia

(use-modules (guix packages)
             (guix download)
             (guix git-download)
             (guix build-system cargo)
             (guix licenses)
             ((guix licenses) #:prefix license:)
             (gnu packages crates-io)
             (gnu packages rust)
             (gnu packages rust-apps))

(define-public eclexia
  (package
    (name "eclexia")
    (version "0.1.0")
    (source
     (origin
       (method git-fetch)
       (uri (git-reference
             (url "https://github.com/hyperpolymath/eclexia")
             (commit (string-append "v" version))))
       (file-name (git-file-name name version))
       (sha256
        (base32
         "0000000000000000000000000000000000000000000000000000"))))
    (build-system cargo-build-system)
    (arguments
     `(#:cargo-inputs
       (("rust-clap" ,rust-clap-4)
        ("rust-miette" ,rust-miette-7)
        ("rust-rustyline" ,rust-rustyline-14)
        ("rust-smol-str" ,rust-smol-str-0.2)
        ("rust-glob" ,rust-glob-0.3)
        ("rust-toml" ,rust-toml-0.8)
        ("rust-serde" ,rust-serde-1)
        ("rust-serde-json" ,rust-serde-json-1)
        ("rust-reqwest" ,rust-reqwest-0.11)
        ("rust-sha2" ,rust-sha2-0.10)
        ("rust-tar" ,rust-tar-0.4))
       #:cargo-development-inputs
       (("rust-proptest" ,rust-proptest-1)
        ("rust-quickcheck" ,rust-quickcheck-1))
       #:install-source? #f
       #:tests? #t))
    (native-inputs
     (list rust `(,rust "cargo")))
    (home-page "https://eclexia.org")
    (synopsis "Resource-aware programming language with shadow pricing")
    (description
     "Eclexia is a programming language designed for resource-aware computing.
It makes computational resources (energy, time, memory) first-class citizens
in the type system and uses shadow prices from linear programming to guide
adaptive execution.  Eclexia enables carbon-aware scheduling, battery-conscious
mobile apps, and cost-optimized cloud services through built-in resource
tracking and economic optimization.")
    (license (list license:pmpl-1.0-or-later))))

eclexia
