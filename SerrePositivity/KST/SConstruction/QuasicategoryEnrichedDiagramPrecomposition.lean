module
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramOrdinaryFunctor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramRestriction

/-! # 全高次比較の圏での豊穣前合成と評価
概要：全 Hom に自然な比較の圏に、同じ豊穣関手での前合成と各対象での評価を与える。
方針：既存の全高次比較の前合成を、同じ成分の恒等・合成と束ねる。
規約：添字圏の宇宙を制限しない。使われ方：元の単体的 S• 図式の厳密 dg 入力への制限。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.InfinityCategories
variable {C : Type v} {L : Type w} [Category.{u} C] [SimplicialCategory C]
  [Category.{u} L] [SimplicialCategory L]

/-- 元の全高次比較を、同じ豊穣関手で全成分について前合成する通常の関手。 -/
def quasicategoryEnrichedPrecompositionFunctor (R : EnrichedFunctor SSet.{u} L C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory L where
  obj F := R.comp SSet F
  map η := η.precompose R
  map_id F := by
    apply Subtype.ext
    funext X
    rfl
  map_comp η θ := by
    apply Subtype.ext
    funext X
    rfl

/-- 元の全高次比較を、同じ一対象の実 quasicategory と実単体的射に評価する。 -/
def quasicategoryEnrichedEvaluationFunctor (X : C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} where
  obj F := F.obj X
  map η := η.val X
  map_id _F := rfl
  map_comp _η _θ := rfl

end SerrePositivity.KST.SConstruction
