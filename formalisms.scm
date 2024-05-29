(define-module (gnu packages formalisms)
  #:use-module (guix packages)
  #:use-module (guix build-system agda)
  #:use-module (guix licenses)
	#:use-module (gnu packages agda)
	#:use-module (guix git-download)
  #:use-module (gnu packages gawk))

(define-public formalisms
	(package
	 (name "formalisms")
	 (version "0.0.1")
   (source
		(origin
		 (sha256 (base32 "0xwgm2mfl2pxipsv31bin8p14y1yhd9n27lv3clvsxd4z9yc034m"))
		 (method git-fetch)
		 (uri (git-reference
					 (url "https://github.com/jyallop/formalisms")
					 (commit "1dfd92dff1717a7b2255627856ec89ca6bb869b6")))))
	 (synopsis "A simple ski jump game")
	 (description "A ski jump game built with the bevy engine using rust")

	 (home-page "blah")
	 (propagated-inputs
		(list agda-stdlib))
	 (build-system agda-build-system)
	 (license gpl3+)))

formalisms


