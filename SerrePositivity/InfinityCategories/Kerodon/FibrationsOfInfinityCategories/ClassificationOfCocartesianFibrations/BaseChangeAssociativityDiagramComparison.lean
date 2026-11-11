module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeAssociativityEnriched
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeAssociativityDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeDiagramComparison
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.NerveCocartesianCoherentUnit

/-!
概要：同じ底変換結合同型を、底全体と元の全高次 Hom に同時に自然な図式比較にする。
方針：元の豊穣比較と底の全射に関する自然性を、そのまま束ねる。
規約：一つの fibration で評価すると、既存の同じ QCat 値の結合比較を回収する。
使われ方：分類 Hom の比較 span の合成と Segal 制限への接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の底変換結合同型は、底全体と元の全 fibration の全相対 Hom に同時に自然。 -/
def cocartesianBaseChangeAssociativityDiagramComparison
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram A).precompose
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap l))))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram A).precompose
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap (l ⋙ k)))) where
  app a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityEnrichedComparison l k a
  naturality f p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent_naturality p.val.hom l k f

/-- 元の fibration での同じ図式比較は、既存の元の QCat 値結合比較そのもの。 -/
lemma cocartesianBaseChangeAssociativityDiagramComparison_evaluate
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C)) :
    Functor.whiskerRight ((cocartesianBaseChangeAssociativityDiagramComparison l k).evaluate p)
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget =
    Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityQCat p.val.hom l k)
      _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.qCatForget := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
