import Lake
open Lake DSL

require "nomeata" / "calcify" @ git "master"

-- Cf. https://github.com/lurk-lab/RustFFI.lean

package egg where
  srcDir := "Lean"
  -- See https://github.com/leanprover/lean4/tree/master/src/lake#github-release-builds
  preferReleaseBuild := true
  releaseRepo?       := none
  buildArchive?      := none

@[default_target]
lean_lib Egg where
  -- This enables the interpreter to run functions marked `@[extern]`.
  precompileModules := true

target importTarget pkg : System.FilePath :=
  pkg.afterBuildCacheAsync do
    let oFile := pkg.buildDir / "c" / "ffi.o"
    let srcJob ← inputTextFile <| pkg.dir / "C" / "ffi.c"
    buildFileAfterDep oFile srcJob fun srcFile => do
      let flags := #["-I", toString (← getLeanIncludeDir), "-fPIC"]
      compileO oFile srcFile flags

extern_lib ffi pkg := do
  let job ← fetch <| pkg.target ``importTarget
  let libFile := pkg.sharedLibDir / nameToStaticLib "ffi"
  buildStaticLib libFile #[job]

extern_lib egg_for_lean pkg := do
  pkg.afterBuildCacheAsync do
    let name      := nameToStaticLib "egg_for_lean"
    let srcPath   := pkg.dir / "Rust" / "Egg" / "target" / "release" / name
    let tgtPath   := pkg.sharedLibDir / name
    let traceFile := pkg.buildDir / "rust" / "egg.trace"
    let _ ← buildUnlessUpToDate? traceFile (← getTrace) traceFile do
      proc {
        cmd := "cargo",
        args := #["rustc", "--release", "--", "-C", "relocation-model=pic"],
        cwd := pkg.dir / "Rust" / "Egg"
      }
      IO.FS.createDirAll pkg.sharedLibDir
      IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
    return pure tgtPath

extern_lib slotted_for_lean pkg := do
  pkg.afterBuildCacheAsync do
    let name := nameToStaticLib "slotted_for_lean"
    let srcPath := pkg.dir / "Rust" / "Slotted" / "target" / "release" / name
    let tgtPath := pkg.sharedLibDir / name
    let traceFile := pkg.buildDir / "rust" / "slotted.trace"
    let _ ← buildUnlessUpToDate? traceFile (← getTrace) traceFile do
      proc {
        cmd := "cargo",
        args := #["rustc", "--release", "--", "-C", "relocation-model=pic"],
        cwd := pkg.dir / "Rust" / "Slotted"
      }
      IO.FS.createDirAll pkg.sharedLibDir
      IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
    return pure tgtPath

@[test_driver]
lean_exe TestDriver where
  srcDir := "Egg/Tests"
