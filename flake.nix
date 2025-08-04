
{
  description = "A Nix-flake-based Lake development environment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forEachSupportedSystem = f: nixpkgs.lib.genAttrs supportedSystems (system: f {
        pkgs = import nixpkgs { inherit system; };
      });
    in
    {
      devShells = forEachSupportedSystem ({ pkgs }:
        let python = pkgs.python3.withPackages(ps: with ps; [leanblueprint pip]);
        in
        {
        default = pkgs.mkShell {
          packages = with pkgs; [
            ##########
            elan # Build Project (Lean4)
            ###
            python # Serve documentation
          ];
        };
      });
    };
}
