{
  # Development shell only; CI uses plain cabal/GHC and the Isabelle container.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs =
    { self, nixpkgs }:
    let
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
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

              actionlint
              shellcheck

              jq
              nodejs
              pkg-config
              zlib
            ];

            shellHook = ''
              root="$(git rev-parse --show-toplevel 2>/dev/null)"

              if [ -n "$root" ]; then
                git -C "$root" config core.hooksPath .githooks
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
