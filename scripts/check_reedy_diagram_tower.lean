import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationTower
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionComparison
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DegreeFactorizationStep
import Lean.Util.CollectAxioms

universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]

-- An actual coherent tower yields an actual global diagram, on all morphisms.
example (T : DiagramTower r C) : J ⥤ C := T.toFunctor

example (T : DiagramTower r C) (n : ℕ) :
    T.stage n ≅ lowerInclusion r n ⋙ T.toFunctor := T.restrictionIso n

example {T S U : DiagramTower r C} (m : T.Map S) (m' : S.Map U) :
    (m.comp m').toNatTrans = m.toNatTrans ≫ m'.toNatTrans := m.toNatTrans_comp m'

-- Reconstruction of a given functor is checked on every morphism.
example (F : J ⥤ C) {j k : J} (f : j ⟶ k) :
    (DiagramTower.ofFunctor r F).toFunctor.map f = F.map f :=
  DiagramTower.ofFunctor_toFunctor_map r F f

example {F G : J ⥤ C} (τ : F ⟶ G) (K : FactorizationTower r τ) :
    K.leftMap ≫ K.rightMap = τ := K.leftMap_rightMap

example {F G : J ⥤ C} (τ : F ⟶ G) (K : FactorizationTower r τ) (n : ℕ) :
    Functor.whiskerLeft (lowerInclusion r n) K.leftMap =
      K.left.app n ≫ (K.diagram.restrictionIso n).hom := K.leftMap_restriction n

-- Δ and Δop, with no restriction on the model source/value category C.
example (F : SimplexCategory ⥤ C) : (DiagramTower.ofFunctor simplex F).toFunctor ≅ F :=
  DiagramTower.ofFunctorIso simplex F

example (F : SimplexCategoryᵒᵖ ⥤ C) : (DiagramTower.ofFunctor simplexOp F).toFunctor ≅ F :=
  DiagramTower.ofFunctorIso simplexOp F

example (F : J ⥤ C) (j : J) :
    (BoundaryExtension.ofFunctor r j F).toFunctor ≅ adjoinInclusion r j ⋙ F :=
  BoundaryExtension.ofFunctorIso r j F

-- The finite-step output factors the original transformation on the ordinary upper category.
example (j : J) (hinj : Function.Injective r.deg)
    [CategoryTheory.Limits.HasColimitsOfShape (LatchingIndex r j) C]
    [CategoryTheory.Limits.HasLimitsOfShape (MatchingIndex r j) C]
    [CategoryTheory.Limits.HasPushouts C] [CategoryTheory.Limits.HasPullbacks C]
    {F G : J ⥤ C} (τ : F ⟶ G)
    {lowerLeft lowerRight : MorphismProperty (Lower r (r.deg j) ⥤ C)}
    (a : MorphismProperty.MapFactorizationData lowerLeft lowerRight
      (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ))
    {left right : MorphismProperty C}
    (q : MorphismProperty.MapFactorizationData left right
      (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) a)) :
    MorphismProperty.MapFactorizationData ⊤ ⊤
      (Functor.whiskerLeft (upperInclusion r (r.deg j)) τ) :=
  DegreeFactorizationStep.factorizationData r j hinj τ a q

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DiagramTower,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DiagramGluing,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.TowerTransformation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.TowerOfFunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationTower,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DegreeFactorizationStep]
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
  logInfo m!"Reedy diagram-tower audit passed: {count} declarations in {seen.size} modules."
