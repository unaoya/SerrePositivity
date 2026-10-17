import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u w vC uC vJ uJ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel

section GeneralElements
variable {J : Type uJ} [Category.{vJ} J] (P : J ⥤ Type w)
  {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) (x : P.Elements)
example [Finite (Reedy.MatchingIndex r x.obj)] :
    Finite (Reedy.MatchingIndex (Reedy.elementsReedy P r) x) := inferInstance
example [Finite (Reedy.LatchingIndex r x.obj)]
    (hinj : ∀ {i j : J} (f : i ⟶ j), direct f → Function.Injective (P.map f)) :
    Finite (Reedy.LatchingIndex (Reedy.elementsReedy P r) x) :=
  Reedy.elementsLatchingIndex_finite P r hinj x
end GeneralElements

section ArbitrarySimplices
variable (X : SSet.{w}) (s : X.Elementsᵒᵖ)
  {C : Type uC} [Category.{vC} C]
example : Finite (Reedy.LatchingIndex (SimplexIndexFinite.reedy X) s) := inferInstance
example : Finite (Reedy.MatchingIndex (SimplexIndexFinite.reedy X) s) := inferInstance
example (a b : Reedy.LatchingIndex (SimplexIndexFinite.reedy X) s) : Finite (a ⟶ b) := inferInstance
example (a b : Reedy.MatchingIndex (SimplexIndexFinite.reedy X) s) : Finite (a ⟶ b) := inferInstance

-- Finite limits/colimits in an independently sized value category suffice.
example [HasFiniteLimits C] :
    HasLimitsOfShape (Reedy.MatchingIndex (SimplexIndexFinite.reedy X) s) C := inferInstance
example [HasFiniteColimits C] :
    HasColimitsOfShape (Reedy.LatchingIndex (SimplexIndexFinite.reedy X) s) C := inferInstance
end ArbitrarySimplices

section LargeNerveSmallValues
variable {D : Type u} [Category.{v} D] (s : NerveSimplexEndpoint.Index D)
example : Finite (Reedy.LatchingIndex (NerveCoherentFamily.reedy D) s) := inferInstance
example : Finite (Reedy.MatchingIndex (NerveCoherentFamily.reedy D) s) := inferInstance
example : HasColimitsOfShape (Reedy.LatchingIndex (NerveCoherentFamily.reedy D) s) SSet.{w} :=
  inferInstance
example : HasLimitsOfShape (Reedy.MatchingIndex (NerveCoherentFamily.reedy D) s) SSet.{w} :=
  inferInstance

-- The existing recursive lifting theorem applies without a degree-injectivity hypothesis.
variable {A B P Q : NerveSimplexEndpoint.Index D ⥤ SSet.{w}}
  (i : A ⟶ B) (p : P ⟶ Q)
  [∀ s, HasLiftingProperty (Reedy.relativeLatchingMap (NerveCoherentFamily.reedy D) s i)
    (Reedy.relativeMatchingMap (NerveCoherentFamily.reedy D) s p)]
example : HasLiftingProperty i p := Reedy.Lifting.hasLiftingProperty (NerveCoherentFamily.reedy D)
end LargeNerveSmallValues

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsFinite,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexIndexFinite]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some mixed choice modules were not audited"
  logInfo m!"Finite simplex index audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
