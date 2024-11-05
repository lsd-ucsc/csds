let
  pkgs = import <nixpkgs> { };
  drv = pkgs.agdaPackages.mkDerivation {
    pname = "csds";
    meta = { };
    src = pkgs.nix-gitignore.gitignoreSource [ "*.nix" "flake.lock" "result" "build-env" ] ./.;
    buildInputs = [
      pkgs.agdaPackages.standard-library
    ];
  };
in
pkgs.mkShell {
  name = "agda-dev_" + drv.pname;
  buildInputs = drv.buildInputs;
}
