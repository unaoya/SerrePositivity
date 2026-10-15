import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open SerrePositivity.Smith.AccessibleIteration

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

example (T : C ⥤ C) (ε : 𝟭 C ⟶ T) [T.IsCardinalAccessible κ] (j : J) :
    (((SuccStruct.ofNatTrans ε).iterationFunctor J).obj j).IsCardinalAccessible κ :=
  iterationStage_isCardinalAccessible T ε κ j

example (T : C ⥤ C) (ε : 𝟭 C ⟶ T) [T.IsCardinalAccessible κ] :
    ((SuccStruct.ofNatTrans ε).iteration J).IsCardinalAccessible κ :=
  iteration_isCardinalAccessible T ε κ

-- An actual instance of the iteration, without an accessibility premise.
example : ((SuccStruct.ofNatTrans (𝟙 (𝟭 C))).iteration J).IsCardinalAccessible κ :=
  iteration_isCardinalAccessible (𝟭 C) (𝟙 (𝟭 C)) κ

example {D : Type u'} [Category.{v'} D] (F : J ⥤ D ⥤ C)
    [F.IsWellOrderContinuous] (hbot : (F.obj ⊥).IsCardinalAccessible κ)
    (hsucc : ∀ j, ¬IsMax j → (F.obj j).IsCardinalAccessible κ →
      (F.obj (Order.succ j)).IsCardinalAccessible κ) (j : J) :
    (F.obj j).IsCardinalAccessible κ := stages_isCardinalAccessible F κ hbot hsucc j

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleIteration do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No accessible iteration declarations audited"
  logInfo m!"Accessible iteration audit passed: {count} declarations, standard axioms only."
