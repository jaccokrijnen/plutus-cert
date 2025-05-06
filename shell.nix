{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs; [
    coq
    coqPackages.mathcomp
    coqPackages.ExtLib
    coqPackages.QuickChick
    coqPackages.equations
    # ocamlPackages.ocamlbuild
    # ocamlPackages.findlib
    # ocamlPackages.core_unix
    ];
}
