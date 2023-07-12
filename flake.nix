{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    crane = {
      url = "github:ipetkov/crane";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, crane, fenix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        # Switch to nightly toolchain
        craneLib = crane.lib.${system}.overrideToolchain fenix.packages.${system}.complete.toolchain;
        packageDef = with pkgs; {
          src = craneLib.cleanCargoSource ./.;
          buildInputs = with pkgs; [ z3_4_12 cvc5 ];
          nativeBuildInputs = with pkgs; [ rustPlatform.bindgenHook makeWrapper ]
            ++ lib.optionals stdenv.isDarwin [ libiconv ];
        };
        cargoArtifacts = craneLib.buildDepsOnly packageDef;
        cosette-prover = craneLib.buildPackage (packageDef // {
          inherit cargoArtifacts;
          doNotLinkInheritedArtifacts = true;
          postInstall = with pkgs; "wrapProgram $out/bin/cosette-prover --set PATH ${lib.makeBinPath [ cvc5 z3_4_11 ]}";
        });
      in {
        packages.default = cosette-prover;

        devShells.default = pkgs.mkShell {
          inputsFrom = [ cosette-prover ];
          packages = with pkgs; [ rust-analyzer julia-bin jless ] ++ lib.optionals stdenv.isLinux [ linuxPackages.perf ];
        };
      });

  nixConfig = {
    extra-substituters = [ "https://cosette.cachix.org" ];
    extra-trusted-public-keys = [ "cosette.cachix.org-1:d2Pfpw41eAAEZsDLXMnSMjjCpaemLAAxIrLCJaMIEWk=" ];
  };
}
