module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportEnrichedNaturality
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryHomWhisker
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：同じ指定同型の始域・終域の quasicategory 値評価の比較を、全局所 Hom に自然に作る。
方針：元の全高次の豊穣自然性を、閉構造でパラメーター付き評価へ移す。
規約：指定同型と元の豊穣関手を保ち、自然性の追加仮定を置かない。
使われ方：元の結合共役を、分類後の同じ Hom span の輸送へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 同じ指定同型の二つの評価は、元の全高次の Hom に自然な豊穣比較を持つ。 -/
def isoTransportQuasicategoryComparison
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportSourceEnriched SSet.{u} C).comp SSet F)
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportTargetEnriched SSet.{u} C).comp SSet F) := by
  let φ (X : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportObject C) : (F.obj X.source).obj ⟶ (F.obj X.target).obj :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor SSet.{u} F).map X.comparison.hom
  refine ⟨φ, ?_⟩
  intro X Y
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportEnriched_naturality SSet.{u} F X Y
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryHomWhiskerLeft, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryHomWhiskerRight] at h
  change F.map X.source Y.source ≫ (ihom (F.obj X.source).obj).map (φ Y) =
    ((Iso.eHomCongr SSet.{u} X.comparison Y.comparison).hom ≫ F.map X.target Y.target) ≫
      (pre (φ X)).app (F.obj Y.target).obj at h
  have hu := congrArg uncurry h
  rw [uncurry_natural_right, uncurry_pre_app] at hu
  exact hu.symm

/-- 同じ豊穣比較の各成分は、指定同型の実際の関手像として同値。 -/
lemma isoTransportQuasicategoryComparison_component_isQCatEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) (X : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((isoTransportQuasicategoryComparison F).val X) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor SSet.{u} F).mapIso X.comparison
  let eS : (F.obj X.source).obj ≅ (F.obj X.target).obj :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id }
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso eS).isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
