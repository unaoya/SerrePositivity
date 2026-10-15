import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeExtension
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionOfFunctor
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

-- This consumer starts with actual diagrams on J and a factorization below j.
-- The new diagram is constructed; it is not part of the assumptions.
example [HasColimitsOfShape (LatchingIndex r j) C]
    [HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
    {F G : J ⥤ C} (τ : F ⟶ G)
    {lowerLeft lowerRight : MorphismProperty (Lower r (r.deg j) ⥤ C)}
    (a : MorphismProperty.MapFactorizationData lowerLeft lowerRight
      (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ))
    {left right : MorphismProperty C}
    (q : MorphismProperty.MapFactorizationData left right
      (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) a)) :
    MorphismProperty.MapFactorizationData ⊤ ⊤
      (BoundaryExtension.mapOfNatTrans r j τ).toNatTrans :=
  RelativeExtension.diagramFactorization (BoundaryExtension.mapOfNatTrans r j τ) a q

example (d : BoundaryExtension r j H) {x y : Lower r (r.deg j)} (f : x ⟶ y) :
    d.toFunctor.map ((adjoinLower r j).map f) = H.map f := d.toFunctor_map_lower f

section Relative
variable [HasColimitsOfShape (LatchingIndex r j) C]
  [HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {F G : Lower r (r.deg j) ⥤ C} {d : BoundaryExtension r j F}
  {e : BoundaryExtension r j G} {τ : F ⟶ G} (m : d.Map e τ)
  {lowerLeft lowerRight : MorphismProperty (Lower r (r.deg j) ⥤ C)}
  (a : MorphismProperty.MapFactorizationData lowerLeft lowerRight τ)
  {left right : MorphismProperty C}
  (q : MorphismProperty.MapFactorizationData left right (RelativeExtension.map m a))

example : left (RelativeExtension.relativeLeft m a q) := RelativeExtension.relativeLeft_mem m a q

example : right (RelativeExtension.relativeRight m a q) := RelativeExtension.relativeRight_mem m a q

example : (RelativeExtension.leftMap m a q).toNatTrans ≫
    (RelativeExtension.rightMap m a q).toNatTrans = m.toNatTrans :=
  RelativeExtension.leftMap_rightMap m a q

example {x y : Lower r (r.deg j)} (f : x ⟶ y) :
    (RelativeExtension.extension m a q).toFunctor.map ((adjoinLower r j).map f) = a.Z.map f :=
  (RelativeExtension.extension m a q).toFunctor_map_lower f
end Relative

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Subcategory,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Induced,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Adjoin,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionData,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionFunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionTransformation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionBoundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeExtension,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionOfFunctor]
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
