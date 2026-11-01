import scripts.refactor.decl_snapshot
import Lean.Util.NumObjs

open Lean

-- Construct structurally equal terms with different heap sharing before olean
-- serialization can intern them. numObjs checks the fixture itself.
private def buildTree : Nat → Bool → IO Expr
  | 0, _ => pure (mkBVar 0)
  | n+1, share => do
    let left ← buildTree n share
    let right ← if share then pure left else buildTree n share
    return mkApp left right

#eval show IO Unit from do
  let shared ← buildTree 10 true
  let expanded ← buildTree 10 false
  let small ← shared.numObjs
  let large ← expanded.numObjs
  unless small < large do throw (IO.userError "fixture has equal heap sharing")
  let key := DeclSnapshot.fingerprint []
  unless key shared == key expanded do throw (IO.userError "hash depends on heap sharing")
  let (h, distinct, bytes) := key shared
  unless distinct == 11 && bytes == 1024 * 10 + 1023 * 9 do
    throw (IO.userError s!"unexpected counts {distinct}, {bytes}")
  unless h != (key (mkApp shared (mkBVar 1))).1 do throw (IO.userError "child change missed")
  let huge ← buildTree 50 true
  let (_, count, size) := key huge
  unless count == 51 && size == 2^50 * 10 + (2^50-1)*9 do
    throw (IO.userError "large DAG count mismatch")
  IO.println s!"PASS: {small} / {large} heap nodes, same hash; {count} distinct subterms, {size} expanded bytes"
