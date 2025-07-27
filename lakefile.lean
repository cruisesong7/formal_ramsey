import Lake
open Lake DSL

package «formal_ramsey» {
  -- add any package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.18.0-rc1"

require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4"@"v0.0.53"

require trestle from git "https://github.com/dMaggot/trestle"@"cf0dbec15c9ce5f5984305fe7733f708031ba9e7"

@[default_target]
lean_lib «FormalRamsey» {
  -- add any library configuration options here
}
lean_exe «vdWEncoder» {
  srcDir := "code"
  root := `VdWEncoder
}

lean_exe «RamseyEncoder» {
  srcDir := "FormalRamsey/Encodings/CNF"
  root := `RamseyEncoder
}

lean_exe «folkmanEncoder» {
  srcDir := "code"
  root := `FolkmanEncoder
}

script vdW (args) do
  if List.length args != 2
  then IO.println "Usage: lake script run vdW <N> <k>" return 1
  else
    -- IO.println "Building vdWEncoder executable..."
    let buildCmd := "lake build"
    let _ ← IO.Process.run { cmd := "sh", args := #["-c", buildCmd] }
    let exePath := "./build/bin/vdWEncoder"
    -- IO.println s!"Running vdWEncoder executable at: {exePath}"

    let runResult ← IO.Process.spawn {
      cmd := exePath
      args := List.toArray args
    } >>= λ proc => do
      proc.wait
    return runResult

script Ramsey (args) do
  if List.length args != 3
  then IO.println "Usage: lake script run Ramsey <N> <s> <t>" return 1
  else
    -- IO.println "Building ramseyEncoder executable..."
    let buildCmd := "lake build RamseyEncoder"
    let _ ← IO.Process.run { cmd := "sh", args := #["-c", buildCmd] }
    let exePath := ".lake/build/bin/RamseyEncoder"

    let runResult ← IO.Process.spawn {
      cmd := exePath
      args := List.toArray args
    } >>= λ proc => do
      proc.wait
    return runResult

script folkman (args) do
  if List.length args != 4
  then IO.println "Usage: lake script run folkman <N> <S> <T> <k>" return 1
  else
    -- IO.println "Building folkmanEncoder executable..."
    let buildCmd := "lake build"
    let _ ← IO.Process.run { cmd := "sh", args := #["-c", buildCmd] }
    let exePath := ".build/bin/FolkmanEncoder"
    -- IO.println s!"Running folkmanEncoder executable at: {exePath}"

    let runResult ← IO.Process.spawn {
      cmd := exePath
      args := List.toArray args
    } >>= λ proc => do
      proc.wait
    return runResult


  -- script cadical (args) do
  -- if List.length args != 1
  -- then IO.println "Usage: lake script run cadical <cnf>" return 1
  -- else
    --   let cadicalPath := System.FilePath.mk "../../../../../SAT/cadical/build/cadical" -- Update this path
  --   let runResult ← IO.Process.spawn {
  --   cmd := externalExePath.toString
  --   args := args
  -- } >>= λ proc => do
  --   proc.wait
