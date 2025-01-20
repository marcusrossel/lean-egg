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

def getTests : IO (Array FS.DirEntry) := do
  let testsDir := (← currentDir) / "Lean"/ "Egg" / "Tests"
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

def runTest (file : FS.DirEntry) : IO TestResult := do
  if let some err ← buildResult then
    return .failure err
  else if ← fileContainsSorry file then
    return .sorry
  else
    return .success
where
  buildResult : IO (Option String) := do
    let cfg := IO.Process.StdioConfig.mk IO.Process.Stdio.null IO.Process.Stdio.null IO.Process.Stdio.null
    let filename := file.fileName.replace ".lean" ""
    let filename := String.join ["Egg.Tests.«", filename, "»"]
    let args := (List.toArray ["build", filename])
    let cwd := some (← IO.Process.getCurrentDir)
    let spawn_args := IO.Process.SpawnArgs.mk cfg "lake" args cwd Array.empty false
    let output ← IO.Process.output spawn_args
    -- let _ := ← IO.println output.exitCode
    -- let _ := ← IO.println output.stdout
    -- let _ := ← IO.println output.stderr
    let out := if output.exitCode == 0 then some output.stdout else none
    pure out

def main (args : List String) : IO Unit := do
  for test in ← getTests do
    match ← runTest test with
    | .success     => println s!"✅ {testName test}"
    | .sorry       => println s!"🟡 {testName test}"
    | .failure msg => println s!"❌ {testName test}{if args.contains "ci" then s!"\n{msg}" else ""}"
