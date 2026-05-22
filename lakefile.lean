import Lake
open Lake DSL

package «formal_ramsey» {
  -- add any package configuration options here
}

require trestle from git "https://github.com/FormalSAT/trestle"@"853ce034ff4a5081d19ccc250d5780d4b7e718ec"

require simpler_graph from git "https://gitlab.com/dmaggot/simpler_graph"@"235a1ab"

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

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "a41d5eb"
