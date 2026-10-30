module

public import Lean
public import Lake.Check.Util

/-! Exact comparison of the compiled theorem types and their transitive statement
constants. This catches copy drift and generated-helper name differences without
exporting proofs. It does not replace sandboxed Comparator or independent kernels. -/

@[expose] public section

open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json")
  let strings ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let targets := strings.map String.toName
  let challenge ← importModules #[{module := `Challenge}] {}
  let solution ← importModules #[{module := `Solution}] {}
  let mut work : Array Name := #[]
  for target in targets do
    let some (.thmInfo c) := challenge.find? target | throw <| IO.userError s!"Missing Challenge theorem {target}"
    let some (.thmInfo s) := solution.find? target | throw <| IO.userError s!"Missing Solution theorem {target}"
    unless c.toConstantVal == s.toConstantVal do
      throw <| IO.userError s!"Statement differs: {target}"
    work := work ++ c.type.getUsedConstants
  let mut checked : Std.HashSet Name := {}
  while !work.isEmpty do
    let target := work.back!
    work := work.pop
    if checked.contains target then continue
    let some c := challenge.find? target | throw <| IO.userError s!"Missing Challenge dependency {target}"
    let some s := solution.find? target | throw <| IO.userError s!"Missing Solution dependency {target}"
    unless c == s do
      throw <| IO.userError s!"Dependency differs: {target}"
    let collect : StateM (Array Name) Unit := Lake.Check.runForUsedConsts s (fun n => modify (·.push n))
    let (_, more) := collect.run #[]
    work := work ++ more
    checked := checked.insert target
  IO.println s!"Structural check: {targets.size} theorem types and {checked.size} transitive statement constants agree exactly."
  IO.println "This does not perform sandboxed Comparator export or independent kernel verification."
