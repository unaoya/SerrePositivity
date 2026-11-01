import scripts.refactor.decl_snapshot

open Lean Elab Command

namespace ProofHashTest
universe u
theorem eqA (α : Sort u) (x : α) : x = x := rfl
theorem eqB (α : Sort u) (x : α) : x = x := rfl

run_cmd do
  let mut env := (← getEnv).unlockAsync
  let name := fun s => ("ProofHashTest." ++ s).toName
  let const := fun s => mkConst (name s)
  -- Local synthetic compiler auxiliaries; do not run the compiler on its own
  -- reserved names. Cyclic unsafe values are only hash fixtures, never executed.
  let nat := mkConst "Nat".toName
  for (n, type, value) in [
      ("innerA._sunfold", nat, mkNatLit 7),
      ("innerB._sunfold", nat, mkNatLit 7),
      ("innerC._sunfold", nat, mkNatLit 8),
      ("outerA._sunfold", nat, const "innerA._sunfold"),
      ("outerB._sunfold", nat, const "innerB._sunfold"),
      ("outerC._sunfold", nat, const "innerC._sunfold"),
      ("recursiveA._unsafe_rec", mkForall Name.anonymous .default nat nat,
        mkLambda "n".toName .default nat (mkApp (const "recursiveA._unsafe_rec") (mkBVar 0))),
      ("recursiveB._unsafe_rec", mkForall Name.anonymous .default nat nat,
        mkLambda "n".toName .default nat (mkApp (const "recursiveB._unsafe_rec") (mkBVar 0)))] do
    let decl := Declaration.defnDecl {
      name := name n, levelParams := [], type, value, hints := .opaque, safety := .unsafe }
    match env.addDeclCore 0 1000 decl none (doCheck := false) with
    | .ok next => env := next
    | .error _ => throwError "could not prepare hash fixture {n}"
  let key := fun (n : String) (ls : List Level) =>
    (DeclSnapshot.fingerprint [] (.const (name n) ls) (some env)).1
  unless key "eqA" [.zero] == key "eqB" [.zero] do
    throwError "theorem names leaked into hash"
  unless key "eqA" [.zero] != key "eqB" [.succ .zero] do
    throwError "theorem universe instantiation was lost"
  unless key "outerA._sunfold" [] == key "outerB._sunfold" [] do
    throwError "nested generated references were not expanded"
  unless key "outerA._sunfold" [] != key "outerC._sunfold" [] do
    throwError "changed generated value was lost"
  unless key "recursiveA._unsafe_rec" [] == key "recursiveB._unsafe_rec" [] do
    throwError "recursive generated names leaked into hash"
  logInfo "PASS: instantiated theorem types, recursive expansion, changed values, recursive auxiliaries"

end ProofHashTest
