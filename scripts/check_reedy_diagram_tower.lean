import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationTower
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionComparison
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationSequence
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
import Mathlib.AlgebraicTopology.ModelCategory.Basic
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

section Sequence
open CategoryTheory.Limits
variable [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {left right : MorphismProperty C} (data : MorphismProperty.FunctorialFactorizationData left right)
  (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)
  {F G : J ⥤ C} (τ : F ⟶ G)

-- No degreewise diagram or factorization tower is an assumption here.
example : MorphismProperty.MapFactorizationData ⊤ ⊤ τ :=
  FactorizationSequence.factorizationData r τ hinj hsurj data.factorizationData

example (n : ℕ) :
    lowerMap r (Nat.le_succ n) ⋙
        (FactorizationSequence.stage r τ hinj hsurj data.factorizationData (n + 1)).Z ≅
      (FactorizationSequence.stage r τ hinj hsurj data.factorizationData n).Z :=
  (FactorSuccessor.next r τ hinj data.factorizationData hsurj n
    (FactorizationSequence.stage r τ hinj hsurj data.factorizationData n)).restriction

example (n : ℕ) :
    Functor.whiskerLeft (lowerInclusion r n)
        (FactorizationSequence.factorizationData r τ hinj hsurj data.factorizationData).i =
      (FactorizationSequence.stage r τ hinj hsurj data.factorizationData n).i ≫
        ((FactorizationSequence.diagramTower r τ hinj hsurj data.factorizationData).restrictionIso n).hom :=
  (FactorizationSequence.factorizationTower r τ hinj hsurj data.factorizationData).leftMap_restriction n
end Sequence

-- Both needed simplex directions work for an arbitrary model category, using
-- only its finite limits and colimits and its ordinary factorization axiom.
example [ModelCategory C] {F G : SimplexCategory ⥤ C} (τ : F ⟶ G)
    : MorphismProperty.MapFactorizationData ⊤ ⊤ τ :=
  FactorizationSequence.factorizationData simplex τ
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)
    (MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C))

example [ModelCategory C] {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G)
    : MorphismProperty.MapFactorizationData ⊤ ⊤ τ :=
  FactorizationSequence.factorizationData simplexOp τ
    (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)
    (MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C))

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
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DegreeFactorizationStep,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionRestriction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationSequence]
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
