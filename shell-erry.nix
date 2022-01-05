{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  buildInputs = [
    pkgs.emacs
    pkgs.ripgrep
    pkgs.fd
    pkgs.pandoc
    pkgs.shellcheck
    pkgs.luajitPackages.lua
    pkgs.luajitPackages.luacheck
    pkgs.luajitPackages.lpeg
    pkgs.p7zip
  ];
}
