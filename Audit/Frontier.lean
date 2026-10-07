import HypercubeRamsey

/-!
# Sorry frontier of the target

Walks the values (proofs and definition bodies) of `Erdos181.erdos_181` and of everything they use inside the
project's namespaces, and prints the project declarations whose own value uses `sorryAx` and that are reachable from the
target. Auxiliary declarations (`…._proof_n`, `…match_n`) are reported under their parent.
-/

open Lean Meta

partial def frontierWalk (env : Environment) (roots : List Name) : NameSet × NameSet := Id.run do
  let inProject (n : Name) := (`HypercubeRamsey).isPrefixOf n || (`Erdos181).isPrefixOf n
  let mut seen : NameSet := {}
  let mut sorried : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let deps : Array Name := match ci with
      | .thmInfo t => t.value.getUsedConstants
      | .defnInfo d => d.value.getUsedConstants
      | .opaqueInfo o => o.value.getUsedConstants
      | _ => #[]
    if deps.contains ``sorryAx then
      let parent := (n.componentsRev.dropWhile (fun c => c.toString.startsWith "_proof" ||
        c.toString.startsWith "match_" || c.toString.startsWith "proof_")).reverse
      sorried := sorried.insert (parent.foldl (fun acc c => acc ++ c) Name.anonymous)
    for d in deps do
      if inProject d && !seen.contains d then stack := d :: stack
  return (seen, sorried)

#eval show MetaM Unit from do
  let env ← getEnv
  let (seen, sorried) := frontierWalk env [`Erdos181.erdos_181]
  IO.println s!"FRONTIER reachable={seen.size} sorried={sorried.size}"
  for n in sorried.toList do
    IO.println s!"SORRY {n}"
