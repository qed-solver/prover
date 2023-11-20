{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    z3 = {
      url = "github:Z3Prover/z3";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, crane, fenix, z3 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        # Switch to nightly toolchain
        craneLib = crane.lib.${system}.overrideToolchain fenix.packages.${system}.complete.toolchain;
        z3_4_12 = pkgs.z3_4_12.overrideAttrs (prev: { src = z3; });
        packageDef = with pkgs; {
          src = craneLib.cleanCargoSource ./.;
          buildInputs = with pkgs; [ z3_4_12 cvc5 ];
          nativeBuildInputs = with pkgs; [ rustPlatform.bindgenHook makeWrapper ]
            ++ lib.optionals stdenv.isDarwin [ libiconv ];
        };
        cargoArtifacts = craneLib.buildDepsOnly packageDef;
        qed-prover = craneLib.buildPackage (packageDef // {
          inherit cargoArtifacts;
          doNotLinkInheritedArtifacts = true;
          postInstall = with pkgs; "wrapProgram $out/bin/qed-prover --set PATH ${lib.makeBinPath [ cvc5 z3_4_12 ]}";
        });
      in {
        packages.default = qed-prover;

        devShells.default = pkgs.mkShell {
          inputsFrom = [ qed-prover ];
          packages = with pkgs; [ rust-analyzer julia-bin jless ] ++ lib.optionals stdenv.isLinux [ linuxPackages.perf ];
        };
      });

  nixConfig = {
    extra-substituters = [ "https://cosette.cachix.org" ];
    extra-trusted-public-keys = [ "cosette.cachix.org-1:d2Pfpw41eAAEZsDLXMnSMjjCpaemLAAxIrLCJaMIEWk=" ];
  };
}
