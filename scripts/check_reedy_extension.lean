import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionFunctor
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
import Lean.Util.CollectAxioms

universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {C : Type u'} [Category.{v'} C] (H : Lower r (r.deg j) ⥤ C)

example (a : α) : ReedyStructure (inverse.inverseImage (lowerInclusion r a))
    (direct.inverseImage (lowerInclusion r a)) α := lowerReedy r a

example (d : BoundaryExtension r j H) : Adjoin r j ⥤ C := d.toFunctor

example (d : BoundaryExtension r j H) {x y z : Adjoin r j} (f : x ⟶ y) (g : y ⟶ z) :
    d.toFunctor.map (f ≫ g) = d.toFunctor.map f ≫ d.toFunctor.map g :=
  d.toFunctor.map_comp f g

example [HasColimitsOfShape (LatchingIndex r j) C]
    [HasLimitsOfShape (MatchingIndex r j) C] {left right : MorphismProperty C}
    (q : MorphismProperty.MapFactorizationData left right (lowerBoundary r j H)) :
    Adjoin r j ⥤ C := (boundaryExtension r j H q).toFunctor

example (j : SimplexCategory) (H : Lower simplex (simplex.deg j) ⥤ C)
    (d : BoundaryExtension simplex j H) : Adjoin simplex j ⥤ C := d.toFunctor

example (j : SimplexCategoryᵒᵖ) (H : Lower simplexOp (simplexOp.deg j) ⥤ C)
    (d : BoundaryExtension simplexOp j H) : Adjoin simplexOp j ⥤ C := d.toFunctor

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Subcategory,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Induced,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Adjoin,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionData,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionFunctor]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Reedy extension audit passed: {count} declarations in {seen.size} modules."
