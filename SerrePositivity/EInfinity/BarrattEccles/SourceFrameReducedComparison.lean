module

public import SerrePositivity.EInfinity.BarrattEccles.SourceFrameSpanComparison
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceReducedComparison

/-!
# 元の終域への frame Hom と既存の reduced 比較の一致

概要：恒等右脚の同じ比較は既存 Map^h の比較と自然な終域比較を通じて一致する。
方針：元の右脚ホモトピーと全要素圏の augmentation の自然性を使う。
規約：既存の二射を変更せず、元の全単体を保持する。
使われ方：Map^h の両端点自然性を同じ比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

def algebraSpecialHammockReducedMap (X Y : (operad A).Algebra) :
    nerve (algebraSpecialHammock A X Y) ⟶ algebraReducedHammock A X Y := by
  let := modelCategory A
  exact algebraSpecialThreeArrowInclusionNerveMap A X Y ≫
    nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor ≫
      algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y ≫
        (algebraHammockReductionIso A X Y).hom

lemma mappingSpaceSpecialHammockReducedMap_fac (X Y : (operad A).Algebra) :
    mappingSpaceSpecialHammockNerveMap A X Y ≫ algebraSpecialHammockReducedMap A X Y =
      mappingSpaceReducedHammockNerveMap A X Y := by
  let := modelCategory A
  simp only [mappingSpaceReducedHammockNerveMap, mappingSpaceHammockColimitNerveMap,
    mappingSpaceHammockGraphNerveMap, mappingSpaceWeakThreeArrowNerveMap,
    algebraSpecialHammockReducedMap, Category.assoc]

def sourceFrameReducedHammockNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      algebraReducedHammock A X Y :=
  sourceFrameSpecialHammockNerveMap A X Y ≫ algebraSpecialHammockReducedMap A X Y

lemma sourceFrameReducedHammockNerveMap_targetComparison (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.map (sourceFrameReducedHammockNerveMap A X Y) =
      AnodyneHomotopy.anodyneQ.map (sourceFrameMappingSpaceIndexMap A X Y) ≫
        AnodyneHomotopy.anodyneQ.map (mappingSpaceReducedHammockNerveMap A X Y) := by
  have h := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts (sourceFrameSpecialHammockHomotopy A X Y)
  rw [sourceFrameReducedHammockNerveMap, Functor.map_comp, h, Functor.map_comp,
    Category.assoc, ← Functor.map_comp, mappingSpaceSpecialHammockReducedMap_fac]

def sourceFrameIndexAugmentation (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      SSet.uliftFunctor.{u + 1, u}.obj (((sourceFrameHom A).obj (op X)).obj Y) :=
  FrameHom.SimplexTerminalNerve.liftedAugmentation _

lemma sourceFrameIndexAugmentation_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (sourceFrameIndexAugmentation A X Y)) :=
  FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso _

lemma sourceFrameIndexAugmentation_targetComparison (X Y : (operad A).Algebra) :
    sourceFrameMappingSpaceIndexMap A X Y ≫ mappingSpaceIndexAugmentation A X Y =
      sourceFrameIndexAugmentation A X Y ≫ SSet.uliftFunctor.{u + 1, u}.map
        (((sourceFrameHomComparison A).app (op X)).app Y) :=
  FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality _

def sourceFrameReducedHammockComparison (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.obj
        (SSet.uliftFunctor.{u + 1, u}.obj (((sourceFrameHom A).obj (op X)).obj Y)) ⟶
      AnodyneHomotopy.anodyneQ.obj (algebraReducedHammock A X Y) := by
  have := sourceFrameIndexAugmentation_localized_isIso A X Y
  exact inv (AnodyneHomotopy.anodyneQ.map (sourceFrameIndexAugmentation A X Y)) ≫
    AnodyneHomotopy.anodyneQ.map (sourceFrameReducedHammockNerveMap A X Y)

lemma sourceFrameReducedHammockComparison_fac (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.map (sourceFrameIndexAugmentation A X Y) ≫
        sourceFrameReducedHammockComparison A X Y =
      AnodyneHomotopy.anodyneQ.map (sourceFrameReducedHammockNerveMap A X Y) := by
  have := sourceFrameIndexAugmentation_localized_isIso A X Y
  exact IsIso.hom_inv_id_assoc _ _

lemma sourceFrameReducedHammockComparison_targetComparison (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((sourceFrameHomComparison A).app (op X)).app Y)) ≫
      (mappingSpaceReducedHammockComparisonIso A X Y).hom =
        sourceFrameReducedHammockComparison A X Y := by
  let Q := AnodyneHomotopy.anodyneQ
  have := sourceFrameIndexAugmentation_localized_isIso A X Y
  have h := congrArg Q.map (sourceFrameIndexAugmentation_targetComparison A X Y)
  simp only [Functor.map_comp] at h
  apply (cancel_epi (Q.map (sourceFrameIndexAugmentation A X Y))).mp
  rw [sourceFrameReducedHammockComparison_fac, ← Category.assoc, ← h, Category.assoc,
    mappingSpaceReducedHammockComparisonIso_fac,
    ← sourceFrameReducedHammockNerveMap_targetComparison]

lemma sourceFrameHomComparison_lift_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
      (((sourceFrameHomComparison A).app (op X)).app Y))) :=
  UniverseLift.anodyneQ_map_isIso_of_small _
    (sourceFrameHomComparison_isIso A AnodyneHomotopy.anodyneQ
      SSet.anodyneExtensions.Q_inverts (op X) Y)

lemma sourceFrameReducedHammockComparison_isIso (X Y : (operad A).Algebra) :
    IsIso (sourceFrameReducedHammockComparison A X Y) := by
  rw [← sourceFrameReducedHammockComparison_targetComparison]
  have := sourceFrameHomComparison_lift_localized_isIso A X Y
  infer_instance

lemma sourceFrameReducedHammockNerveMap_weak (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (sourceFrameReducedHammockNerveMap A X Y) := by
  apply FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
  rw [← sourceFrameReducedHammockComparison_fac]
  have := sourceFrameIndexAugmentation_localized_isIso A X Y
  have := sourceFrameReducedHammockComparison_isIso A X Y
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
