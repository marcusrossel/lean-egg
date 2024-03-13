import Lake
open Lake DSL

-- Cf. https://github.com/lurk-lab/RustFFI.lean

package egg where
  srcDir := "Lean"

@[default_target]
lean_lib Egg where
  precompileModules := true

extern_lib egg_for_lean pkg := do
  proc { cmd := "cargo", args := #["rustc", "--release", "--", "-C", "relocation-model=pic"], cwd := pkg.dir / "Rust" }
  let name := nameToStaticLib "egg_for_lean"
  let srcPath := pkg.dir / "Rust" / "target" / "release" / name
  IO.FS.createDirAll pkg.nativeLibDir
  let tgtPath := pkg.nativeLibDir / name
  IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
  return pure tgtPath

require std from git "https://github.com/leanprover/std4" @ "v4.7.0-rc1"
