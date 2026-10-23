module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedKanAction
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplicialOverTestComparison

/-!
概要：相対 Hom の共同評価の実際の作用と、同じ共同反転図式の pointed 輸送。
方針：始域とテスト標的の組を一つの豊穣圏とし、共通解像と全対象の反転比較を使う。
規約：テスト標的を固定しない。元の始域の射影に充填性を要求しない。
使われ方：coherent 自然性の四角形の二段輸送を、同じ相対 Hom の共同図式へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}

/-- 相対 Hom の双関手を、同じ共通解像上で反転した値の共同図式へ移す。 -/
def simplicialOverJointOppositeTest (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) :
    SimplicialNerve (EdgewiseEnrichedObject
      (SimplicialPairObject Cᵒᵖ (LeftFibrationObject B))) ⟶ SpaceInfinity.{u} :=
  coherentNerveMap (edgewiseEnrichedFunctor (simplicialOverTestBifunctor F)) ≫
    edgewiseOppositeKanInfinityMap

/-- 元の共同評価と反転した共同評価は、全ての始域・標的で一つの関手同型により比較される。 -/
def simplicialOverJointOppositeTestIso
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) :
    FunctorIso (edgewiseEnrichedInfinityMap
      (SimplicialPairObject Cᵒᵖ (LeftFibrationObject B)) ≫ simplicialOverJointTest F)
        (simplicialOverJointOppositeTest F) :=
  edgewiseEnrichedKanDiagramIso (simplicialOverTestBifunctor F)

/-- 同じ反転した共通 Hom で、共同評価の実際の作用が与える辺の族。 -/
def simplicialOverJointActionInterval
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B))
    (X Y : SimplicialPairObject Cᵒᵖ (LeftFibrationObject B)) :
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom X Y))).op ⟶ intervalMappingSpace
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((simplicialOverTestBifunctor F).obj X)))
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((simplicialOverTestBifunctor F).obj Y))) :=
  edgewiseReflectedParameter (SimplicialCategory.sHom X Y) ≫
    kanParameterizedLeftHomInterval (X := (simplicialOverTestBifunctor F).obj X)
      (Y := (simplicialOverTestBifunctor F).obj Y)
      (uncurry ((simplicialOverTestBifunctor F).map X Y))

/-- 共同評価の辺の族は、同じ共同反転図式への coherent Hom の後合成に厳密に一致する。 -/
lemma simplicialOverJointActionInterval_uncurry
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B))
    (X Y : SimplicialPairObject Cᵒᵖ (LeftFibrationObject B)) :
    intervalMappingUncurry (simplicialOverJointActionInterval F X Y) =
      coherentLeftHomInterval (C := EdgewiseEnrichedObject
        (SimplicialPairObject Cᵒᵖ (LeftFibrationObject B))) ⟨X, trivial⟩ ⟨Y, trivial⟩ ≫
          simplicialOverJointOppositeTest F :=
  edgewiseEnrichedKanActionInterval_uncurry (simplicialOverTestBifunctor F) X Y

/-- 共同評価の実際の Hom 作用は、前合成・元の射・後合成の三つの相対射の合成。 -/
lemma simplicialOverTestBifunctor_action_apply
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B))
    (X Y : SimplicialPairObject Cᵒᵖ (LeftFibrationObject B)) {n m : SimplexCategoryᵒᵖ}
    (f : (relativeFunctorSpace X.2.val.hom (F.obj X.1.unop).val.hom).obj n)
    (a : (SimplicialCategory.sHom Y.1.unop X.1.unop).obj n)
    (b : (relativeFunctorSpace Y.2.val.hom X.2.val.hom).obj n)
    (α : n ⟶ m) (z : (F.obj Y.1.unop).val.left.obj m) :
    (((uncurry ((simplicialOverTestBifunctor F).map X Y)).app n (f, a, b)).val.app m α) z =
      (b.val.app m α) ((f.val.app m α) (((F.map Y.1.unop X.1.unop).app n a).val.app m α z)) := by
  change (((uncurry ((simplicialOverTestSource F).map X Y ≫
    curry (simplicialOverTestAction (Opposite.op (F.obj X.1.unop), X.2)
      (Opposite.op (F.obj Y.1.unop), Y.2)))).app n (f, a, b)).val.app m α) z = _
  rw [uncurry_natural_left, uncurry_curry]
  exact simplicialOverTestAction_apply (B := B)
    (Opposite.op (F.obj X.1.unop), X.2) (Opposite.op (F.obj Y.1.unop), Y.2)
    f ((F.map Y.1.unop X.1.unop).app n a) b α z

/-- 同じ共同図式の辺に沿う pointed 輸送を、実際の三つの相対射の合成と比較する。 -/
def simplicialOverJointAction_transportIso
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B))
    (X Y : SimplicialPairObject Cᵒᵖ (LeftFibrationObject B)) {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj ((simplicialOverTestBifunctor F).obj X).obj)
    (t : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom X Y))).op) :
    FunctorIso
      (lift x (t ≫ edgewiseReflectedParameter (SimplicialCategory.sHom X Y)) ≫
        (HomotopyLimits.uliftTensorIso ((simplicialOverTestBifunctor F).obj X).obj
          (SimplicialCategory.sHom X Y)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (uncurry ((simplicialOverTestBifunctor F).map X Y)) ≫
        pointedSpaceLeftResolutionComparison ((simplicialOverTestBifunctor F).obj Y))
      (diagonalFiberTransport pointedSpaceProjection
        (x ≫ pointedSpaceLeftResolutionComparison ((simplicialOverTestBifunctor F).obj X))
        (t ≫ simplicialOverJointActionInterval F X Y)) :=
  pointedSpaceLeftResolution_parametrizedTransportIso
    (X := (simplicialOverTestBifunctor F).obj X) (Y := (simplicialOverTestBifunctor F).obj Y)
    (uncurry ((simplicialOverTestBifunctor F).map X Y))
      x (t ≫ edgewiseReflectedParameter (SimplicialCategory.sHom X Y))

end SerrePositivity.InfinityCategories
