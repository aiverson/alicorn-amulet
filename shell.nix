{ pkgs ? import <nixpkgs> { } }:

with pkgs;

# with callPackage ./lib.nix {
#   inherit (luajitPackages)
#     buildLuarocksPackage dkjson compat53 argparse luafilesystem;
# };

let
  amulet = callPackage (fetchFromGitHub {
    owner = "aiverson";
    repo = "amulet";
    rev = "master";
    sha256 = "0xiizffzj31lpphsn92nbsnpjb12bzpsq796b3nxfg8vchil992f";
  }) { };

in mkShell {
  buildInputs =
    [ luajitPackages.lua luajitPackages.lpeg luajitPackages.luacheck amulet ];
}
