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
        craneLib = crane.lib.${system}.overrideToolchain fenix.packages.${system}.minimal.toolchain;
        packageDef = with pkgs; {
          src = craneLib.cleanCargoSource ./.;
          buildInputs = [ cvc5 ];
          nativeBuildInputs = [ llvmPackages.clang llvmPackages.libclang.lib z3.dev makeWrapper ]
            ++ lib.optionals stdenv.isDarwin [ libiconv ];
          LIBCLANG_PATH = "${llvmPackages.libclang.lib}/lib";
        };
        cargoArtifacts = craneLib.buildDepsOnly packageDef;
        cosette-prover = craneLib.buildPackage (packageDef // {
          inherit cargoArtifacts;
          postInstall = with pkgs; "wrapProgram $out/bin/cosette-prover --prefix PATH : ${cvc5}/bin";
        });
      in {
        defaultPackage = cosette-prover;

        devShell = pkgs.mkShell {
          inputsFrom = [ cosette-prover ];
          packages = with pkgs; [ rust-analyzer ];
        };
      }
    );
}
