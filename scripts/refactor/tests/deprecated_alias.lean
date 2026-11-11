module
public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public meta import Lean.Compiler.LCNF.PhaseExt
public import Mathlib.Tactic
@[expose] public section
set_option linter.deprecated false
namespace IFDeprecatedAliasTests.New
structure Box (α : Type u) where
  val : α
inductive Choice (α : Type u) where
  | one : α → Choice α
  | two : Choice α → Choice α
instance boxInhabited [Inhabited α] : Inhabited (Box α) := ⟨⟨default⟩⟩
def ident {α : Type u} (x : α) := x
@[simp] theorem ident_eq {α : Type u} (x : α) : ident x = x := rfl
end IFDeprecatedAliasTests.New
@[deprecated IFDeprecatedAliasTests.New.Box (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.Box := IFDeprecatedAliasTests.New.Box
@[deprecated IFDeprecatedAliasTests.New.Box.mk (since := "2026-11-05"), match_pattern]
deprecated_alias IFDeprecatedAliasTests.Old.Box.mk := IFDeprecatedAliasTests.New.Box.mk
@[deprecated IFDeprecatedAliasTests.New.Box.val (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.Box.val := IFDeprecatedAliasTests.New.Box.val
@[deprecated IFDeprecatedAliasTests.New.Box.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias IFDeprecatedAliasTests.Old.Box.rec := IFDeprecatedAliasTests.New.Box.rec
@[deprecated IFDeprecatedAliasTests.New.Choice (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.Choice := IFDeprecatedAliasTests.New.Choice
@[deprecated IFDeprecatedAliasTests.New.Choice.one (since := "2026-11-05"), match_pattern]
deprecated_alias IFDeprecatedAliasTests.Old.Choice.one := IFDeprecatedAliasTests.New.Choice.one
@[deprecated IFDeprecatedAliasTests.New.Choice.two (since := "2026-11-05"), match_pattern]
deprecated_alias IFDeprecatedAliasTests.Old.Choice.two := IFDeprecatedAliasTests.New.Choice.two
@[deprecated IFDeprecatedAliasTests.New.ident (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.ident := IFDeprecatedAliasTests.New.ident
@[deprecated (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.ident.eq_1 := IFDeprecatedAliasTests.New.ident.eq_1
@[deprecated (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.ident_eq := IFDeprecatedAliasTests.New.ident_eq
example : IFDeprecatedAliasTests.Old.Box Nat := { val := 3 }
example (b : IFDeprecatedAliasTests.Old.Box Nat) : Nat := b.val
example : IFDeprecatedAliasTests.Old.Box Nat := IFDeprecatedAliasTests.Old.Box.mk 3
example (x : IFDeprecatedAliasTests.Old.Choice Nat) : Nat := match x with
 | IFDeprecatedAliasTests.Old.Choice.one n => n
 | IFDeprecatedAliasTests.Old.Choice.two _ => 0
example : IFDeprecatedAliasTests.Old.ident 1 = 1 := by simp [IFDeprecatedAliasTests.Old.ident.eq_1]
example (x : IFDeprecatedAliasTests.Old.Box Nat) : x.val = x.val := by cases x; rfl
namespace IFDeprecatedAliasTests.New
private theorem _root_.IFDeprecatedAliasTests.New.Child.private_eq : 1 = 1 := rfl
example : 1 = 1 := _root_.IFDeprecatedAliasTests.New.Child.private_eq
end IFDeprecatedAliasTests.New

namespace IFDeprecatedAliasTests.Legacy.Child
end IFDeprecatedAliasTests.Legacy.Child
namespace IFDeprecatedAliasTests.New
namespace Child
open IFDeprecatedAliasTests.Legacy.Child
example : True := True.intro
end Child
end IFDeprecatedAliasTests.New

@[deprecated (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.boxInhabited := IFDeprecatedAliasTests.New.boxInhabited

def oldProjection (b : IFDeprecatedAliasTests.Old.Box Nat) : Nat := b.val
#guard oldProjection ⟨3⟩ == 3

def oldPattern (x : IFDeprecatedAliasTests.Old.Choice Nat) : Nat := match x with
 | IFDeprecatedAliasTests.Old.Choice.one n => n
 | IFDeprecatedAliasTests.Old.Choice.two _ => 0
#guard oldPattern (IFDeprecatedAliasTests.Old.Choice.one 7) == 7

open Lean Meta in
run_meta do
  let env ← getEnv
  let pairs := [(`IFDeprecatedAliasTests.Old.Box, `IFDeprecatedAliasTests.New.Box),
    (`IFDeprecatedAliasTests.Old.Box.val, `IFDeprecatedAliasTests.New.Box.val),
    (`IFDeprecatedAliasTests.Old.ident.eq_1, `IFDeprecatedAliasTests.New.ident.eq_1),
    (`IFDeprecatedAliasTests.Old.ident_eq, `IFDeprecatedAliasTests.New.ident_eq)]
  for (old, new) in pairs do
    let oi ← getConstInfo old
    let ni ← getConstInfo new
    unless oi.levelParams == ni.levelParams do throwError "universe parameters changed"
    unless ← withReducible <| isDefEqGuarded oi.type ni.type do throwError "alias type changed"
    unless oi.value? (allowOpaque := true) == some (mkConst new (ni.levelParams.map mkLevelParam)) do
      throwError "alias is not exactly the target constant: {old}; body {oi.value? (allowOpaque := true)}; levels {oi.levelParams} / {ni.levelParams}"
    unless Linter.getDeprecatedNewName env old == some new do throwError "deprecated target missing"
  unless (← getInstancePriority? `IFDeprecatedAliasTests.Old.boxInhabited).isNone do
    throwError "instance registered twice"
  unless (← getInstancePriority? `IFDeprecatedAliasTests.New.boxInhabited).isSome do
    throwError "canonical instance missing"
  let simp ← getSimpTheorems
  if simp.isLemma (.decl `IFDeprecatedAliasTests.Old.ident_eq) then throwError "simp registered twice"

-- Recursive implementation aliases must not compile their parent a second time.
namespace IFDeprecatedAliasTests.New
def choiceDepth {α : Type u} : Choice α → Nat
  | .one _ => 0
  | .two x => choiceDepth x + 1
end IFDeprecatedAliasTests.New

@[deprecated IFDeprecatedAliasTests.New.choiceDepth (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.choiceDepth := IFDeprecatedAliasTests.New.choiceDepth
@[deprecated IFDeprecatedAliasTests.New.choiceDepth._unsafe_rec (since := "2026-11-05")]
deprecated_alias IFDeprecatedAliasTests.Old.choiceDepth._unsafe_rec :=
  IFDeprecatedAliasTests.New.choiceDepth._unsafe_rec

#guard IFDeprecatedAliasTests.Old.choiceDepth
  (IFDeprecatedAliasTests.Old.Choice.two (IFDeprecatedAliasTests.Old.Choice.one 7)) == 1
#guard IFDeprecatedAliasTests.New.choiceDepth
  (IFDeprecatedAliasTests.New.Choice.two (IFDeprecatedAliasTests.New.Choice.one 7)) == 1

open Lean Meta in
run_meta do
  let env ← getEnv
  for n in [`IFDeprecatedAliasTests.Old.choiceDepth,
      `IFDeprecatedAliasTests.Old.choiceDepth._unsafe_rec] do
    if isNoncomputable env n then throwError "computable alias became noncomputable: {n}"
  let (decls, names) := Compiler.LCNF.declOrderExt.getState env
  unless decls.length == names.size do throwError "duplicate native declarations for recursive alias"
