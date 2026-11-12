module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConstantSourceRelativeShapeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningMappingNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SourceConstantShapeRestriction

/-!
概要：元の定値始域比較は、実切断の形状制限と全族で自然。
方針：既存の相対 unstraightening の底変換同型を同じ相対指数同型へ写す。
規約：同型は変換空間全体の写像の間で作り、各頂点だけにしない。
使われ方：元の錐の切断写像と形状制限を結ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 定値始域を正規化しても、元の相対写像空間の底変換の全族同型を使える。 -/
def constantSourceMappingSpace_baseChangeIso {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso
      (leftUnstraighteningMappingSpaceMap (SSet.const z) F ≫
        constantSourceRelativeShapePre F i z)
      ((sourceConstantShapeRestriction i F z ≫
        leftUnstraighteningMappingSpaceMap (SSet.const z) (i ≫ F)) ≫
        relativeFunctorSquarePost (leftUnstraighteningProjection (i ≫ F))
          (leftUnstraighteningProjection F) i (leftUnstraighteningMap (i ≫ F) F i rfl)
          (leftUnstraighteningMap_projection _ _ _ _)
          (leftUnstraighteningProjection (SSet.const z : K ⟶ _))) := by
  have h := leftUnstraighteningMappingSpaceMap_baseChangeIso (SSet.const z) F i
  simpa only [SSet.comp_const, leftUnstraighteningOverBaseMap,
    constantSourceRelativeShapePre, leftUnstraighteningTransformationRestriction,
    sourceConstantShapeRestriction, intervalMappingPost, intervalMappingPostOfEq,
    intervalMappingCurryOfEndpoints] using h

/-- 元の定値始域比較と実切断の制限は、全変換空間からの写像として同型。 -/
def coherentConstantSourceMap_shapeIso {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso
      (coherentConstantSourceMap F z ≫
        (ihom (vertexFiber pointedSpaceProjection z)).map
          (unstraighteningSectionsRestriction F i))
      (sourceConstantShapeRestriction i F z ≫ coherentConstantSourceMap (i ≫ F) z) := by
  have h := FunctorIso.postcomp (constantSourceMappingSpace_baseChangeIso F i z)
    (constantSourceRestrictedRelativeIso F i z).hom
  rw [constantSourceRelativeShapePre_comparison,
    constantSourceRelativeShapePost_comparison] at h
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h
  let e := (ihom (vertexFiber pointedSpaceProjection z)).mapIso
    (unstraighteningSectionsRestrictionTargetIso F i)
  have h' := FunctorIso.postcomp h e.inv
  simpa only [coherentConstantSourceMap, Category.assoc,
    e, CategoryTheory.Functor.mapIso_inv, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] using h'

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
