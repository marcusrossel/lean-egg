import Lake
open IO

-- See: https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/String.2EisInfixOf
def String.isInfixOf (needle : String) (hey : String) := Id.run do
  let mut i := hey.mkIterator
  while not i.atEnd do
    if needle.isPrefixOf i.remainingToString
    then return true
    else i := i.next
  return false

def ciFlag := "ci"

def getTests : IO (Array FS.DirEntry) := do
  let testsDir := (← currentDir) / "Lean" / "Egg" / "Tests"
  let entries ← testsDir.readDir
  let files ← entries.filterM fun e => return !(← e.path.isDir)
  let leanFiles := files.filter (·.fileName.endsWith ".lean")
  let tests := leanFiles.filter (!·.fileName.startsWith "WIP")
  return tests.insertionSort (·.fileName < ·.fileName)

def testName (file : FS.DirEntry) : String :=
  file.fileName.stripSuffix ".lean"

inductive TestResult where
  | success
  | sorry
  | failure (msg : String)

def fileContainsSorry (file : FS.DirEntry) : IO Bool :=
  return "sorry".isInfixOf (← FS.readFile file.path)

def runFile (file : FS.DirEntry) : IO TestResult := do
  if let some err ← buildResult then
    return .failure err
  else if ← fileContainsSorry file then
    return .sorry
  else
    return .success
where
  buildResult : IO (Option String) := do
    let output ← Process.output {
      stdin := .null, stdout := .null, stderr := .null,
      cmd := "lake", args := #["build", s!"Egg.Tests.«{testName file}»"]
    }
    if output.exitCode = 0 then
      return none
    else
      return output.stdout

def runTest (test : FS.DirEntry) (printErr : Bool) : IO Unit := do
  match ← runFile test with
  | .success     => println s!"✅ {testName test}"
  | .sorry       => println s!"🟡 {testName test}"
  | .failure msg => println s!"❌ {testName test}{if printErr then s!"\n{msg}" else ""}"

def runAllTests (printErr : Bool) : IO Unit := do
  for test in ← getTests do
    runTest test printErr

def runSingleTest (name : String) : IO Unit := do
  runTest (printErr := true) {
    root := (← currentDir) / "Lean" / "Egg" / "Tests",
    fileName := s!"{name}.lean"
  }

def main (args : List String) : IO Unit := do
  assert! args.length ≤ 1
  match args[0]? with
  | none      => runAllTests (printErr := false)
  | some "ci" => runAllTests (printErr := true)
  | some test => runSingleTest test
