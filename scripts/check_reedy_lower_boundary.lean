import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerTransformation
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
import Lean.Util.CollectAxioms

universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) {C : Type u'} [Category.{v'} C]

example (H : Lower r (r.deg j) ⥤ C)
    [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
    (f : LatchingIndex r j) (g : MatchingIndex r j) :
    colimit.ι (latchingSourceLower r j ⋙ H) f ≫ lowerBoundary r j H ≫
      limit.π (matchingTargetLower r j ⋙ H) g = H.map (crossing r j f g) :=
  ι_lowerBoundary_π r j H f g

example {F G : J ⥤ C}
    (ℓ : lowerInclusion r (r.deg j) ⋙ F ⟶ lowerInclusion r (r.deg j) ⋙ G)
    [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C] :
    latchingExtension r j ℓ ≫ (matchingComparison r j).app G =
      (latchingComparison r j).app F ≫ matchingExtension r j ℓ :=
  latching_matching_extension r j ℓ

example {F G : SimplexCategory ⥤ C} (app : ∀ j, F.obj j ⟶ G.obj j)
    (hepi : ∀ {i j} (f : i ⟶ j), Epi f → F.map f ≫ app j = app i ≫ G.map f)
    (hmono : ∀ {i j} (f : i ⟶ j), Mono f → F.map f ≫ app j = app i ≫ G.map f) : F ⟶ G :=
  natTransOfReedy simplex app hepi hmono

-- A diagram only on lower degrees is enough; no assigned value at j is assumed.
example [HasFiniteLimits C] [HasFiniteColimits C] (j : SimplexCategoryᵒᵖ)
    (H : Lower simplexOp (simplexOp.deg j) ⥤ C) :
    colimit (latchingSourceLower simplexOp j ⋙ H) ⟶
      limit (matchingTargetLower simplexOp j ⋙ H) := lowerBoundary simplexOp j H

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Degree,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Boundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerTransformation]
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
  if modules.size != expected.size then throwError "Not all lower-boundary modules were audited"
  logInfo m!"Lower Reedy boundary audit passed: {count} declarations in 3 modules, standard axioms only."
