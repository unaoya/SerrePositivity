import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u w vJ uJ vD uD
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

-- Actual categorical equivalences, with no finite/smallness hypotheses.
example : Reedy.MatchingIndex (Reedy.elementsReedy P r) x ≌ Reedy.MatchingIndex r x.obj :=
  Reedy.elementsMatchingEquivalence P r x
example : Reedy.LatchingIndex (Reedy.elementsReedy P r).op (Opposite.op x) ≌
    Reedy.LatchingIndex r.op (Opposite.op x.obj) := Reedy.elementsLatchingOpEquivalence P r x
example : Reedy.elementsMatchingForget P r x ⋙ Reedy.matchingTarget r x.obj =
    Reedy.matchingTarget (Reedy.elementsReedy P r) x ⋙ Functor.Elements.π P :=
  Reedy.elementsMatchingTarget_eq P r x
end GeneralElements

section Boundary
variable (X : SSet.{w}) (s : X.Elementsᵒᵖ)

-- Independent index and value universes, and the actual comparison arrow.
example : (Reedy.latchingEvaluation (SimplexIndexFinite.reedy X) s).obj
    (SimplexLatchingBoundary.parameters.{w, v} X) ≅
      (SSet.boundary.{v} (SimplexLatchingBoundary.degree X s).len).toSSet :=
  SimplexLatchingBoundary.boundaryIso X s
example : Arrow.mk ((Reedy.latchingComparison (SimplexIndexFinite.reedy X) s).app
    (SimplexLatchingBoundary.parameters.{w, v} X)) ≅
      Arrow.mk (SSet.boundary.{v} (SimplexLatchingBoundary.degree X s).len).ι :=
  SimplexLatchingBoundary.boundaryArrowIso X s
example : (SimplexLatchingBoundary.boundaryIso.{w, v} X s).hom ≫
    (SSet.boundary.{v} (SimplexLatchingBoundary.degree X s).len).ι =
      (Reedy.latchingComparison (SimplexIndexFinite.reedy X) s).app
        (SimplexLatchingBoundary.parameters.{w, v} X) :=
  SimplexLatchingBoundary.boundaryIso_fac X s
end Boundary

section CoherentParameter
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)

-- The actual parameter diagram from the coherent-family definition is Reedy cofibrant.
example : Reedy.reedyLeft (NerveCoherentFamily.reedy D) (cofibrations SSet.{w})
    (initial.to (NerveCoherentFamily.simplices.{vD, uD, w} D)) :=
  SimplexLatchingBoundary.reedy_cofibrant (nerve D) hcof

-- Natural lifting uses the proved left condition; only the value-side right condition remains.
variable {P Q : NerveSimplexEndpoint.Index D ⥤ SSet.{w}} (p : P ⟶ Q)
  (hp : Reedy.reedyRight (NerveCoherentFamily.reedy D) (trivialFibrations SSet.{w}) p)
example : HasLiftingProperty (initial.to (NerveCoherentFamily.simplices.{vD, uD, w} D)) p :=
  Reedy.lifting_of_reedy (NerveCoherentFamily.reedy D) (cofibrations SSet.{w})
    (trivialFibrations SSet.{w}) _ _
    (SimplexLatchingBoundary.reedy_cofibrant (nerve D) hcof) hp
end CoherentParameter

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsMatchingEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary]
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
  logInfo m!"Simplex latching boundary audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
