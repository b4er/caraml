{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

    afp = {
      url = "https://www.isa-afp.org/release/afp-2026-07-21.tar.gz";
      flake = false;
    };
  };

  outputs =
    { self, nixpkgs, afp }:
    let
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;

      verifiedFor = pkgs:
        pkgs.stdenv.mkDerivation {
          pname = "caraml-verified";
          version = "0.1.0";

          src = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [
              ./ROOTS
              ./root.bib
              ./prelude
              ./syntax
              ./spec
              ./core
              ./typing
              ./haskell/ROOT
              ./haskell/Export.thy
            ];
          };

          nativeBuildInputs = [ pkgs.isabelle ];

          buildPhase = ''
            runHook preBuild

            export HOME=$TMPDIR
            user_home="$(isabelle getenv -b ISABELLE_HOME_USER)"
            mkdir -p "$user_home/etc"
            cat > "$user_home/etc/settings" <<EOF
            ISABELLE_TMP_PREFIX="$TMPDIR/isabelle"
            ML_OPTIONS="--minheap 1000 --maxheap 16000"
            EOF

            threads=$((NIX_BUILD_CORES < 8 ? NIX_BUILD_CORES : 8))
            isabelle build -j1 -o threads=$threads -v \
              -d ${afp}/thys -d . -e CaraML_Export

            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            cp -r haskell/verified $out
            runHook postInstall
          '';
        };

      abbreviationsFor = pkgs: pkgs.callPackage ./editors/abbreviations.nix { };

      caramlCabal = pkgs: pkgs.haskellPackages.callCabal2nix "caraml" ./haskell { };

      caramlFor = pkgs:
        pkgs.haskell.lib.overrideCabal (caramlCabal pkgs) (_: {
          preConfigure = ''
            rm -rf verified
            cp -r ${verifiedFor pkgs} verified
            chmod -R u+w verified
            install -m644 ${abbreviationsFor pkgs}/haskell/src/CaraML/Lsp/Abbreviations.hs \
              src/CaraML/Lsp/
          '';
        });
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        rec {
          verified = verifiedFor pkgs;
          abbreviations = abbreviationsFor pkgs;
          caraml = pkgs.haskell.lib.justStaticExecutables (caramlFor pkgs);
          default = caraml;
        }
      );

      apps = forAllSystems (system: {
        default = {
          type = "app";
          program = "${self.packages.${system}.caraml}/bin/caraml";
        };
      });

      devShells = forAllSystems (system:
        let
          pkgs   = import nixpkgs { inherit system; };
          hsPkgs = pkgs.haskellPackages;
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              hsPkgs.ghc
              hsPkgs.cabal-install
              hsPkgs.haskell-language-server
              hsPkgs.fourmolu
              hsPkgs.hlint
              hsPkgs.cabal-fmt

              jq
              nodejs
              pkg-config
              zlib
            ];

            shellHook = ''
              root="$(git rev-parse --show-toplevel 2>/dev/null)"

              if [ -d "$root/editors" ]; then
                cp -r --no-preserve=mode ${abbreviationsFor pkgs}/. "$root/"
              fi

              if [ -d "$root/haskell" ]; then
                if bin="$(cabal list-bin --project-dir="$root/haskell" caraml 2>/dev/null)" && [ -x "$bin" ]; then
                  export PATH="$(dirname "$bin"):$PATH"
                fi
              fi

              unset bin root
            '';
          };
        }
      );
    };
}
