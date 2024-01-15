import Lake
open Lake DSL

-- Cf. https://github.com/lurk-lab/RustFFI.lean

package «lean-egg» where
  srcDir := "Lean"

@[default_target]
lean_lib Egg where
  precompileModules := true

target importTarget pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "C" / "ffi.c"
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", toString (← getLeanIncludeDir)]
    compileO "ffi.c" oFile srcFile flags

extern_lib ffi pkg := do
  let job ← fetch <| pkg.target ``importTarget
  let libFile := pkg.nativeLibDir / nameToStaticLib "ffi"
  buildStaticLib libFile #[job]

extern_lib egg_for_lean pkg := do
  proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir / "Rust" }
  let name := nameToStaticLib "egg_for_lean"
  let srcPath := pkg.dir / "Rust" / "target" / "release" / name
  IO.FS.createDirAll pkg.nativeLibDir
  let tgtPath := pkg.nativeLibDir / name
  IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
  return pure tgtPath

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
