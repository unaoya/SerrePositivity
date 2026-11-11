module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportQuasicategoryDiagramComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsoTransportSectionComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportEnrichedDiagram

/-!
概要：元の cocartesian fibration の指定同型の比較は、全局所 Hom と底全体に同時に自然。
方針：元の strict transport の豊穣図式に、同じ指定同型の二つの評価を前合成する。
規約：元の全 Hom の源と既存の section 比較成分を保持する。
使われ方：結合共役と既存の結合 Hom 輸送の全局所比較を実現する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の全局所 Hom と底全体の射に同時に自然な、指定同型の strict transport の比較。 -/
def cocartesianIsoTransportDiagramComparison (A : Type u) [Category.{u} A] :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram A).precompose
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportSourceEnriched SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve A))))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram A).precompose
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportTargetEnriched SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve A)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isoTransportQuasicategoryDiagramComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram A)

/-- 同じ全局所比較の元の二重引き戻しでの成分は、既存の結合比較そのもの。 -/
lemma cocartesianIsoTransportDiagramComparison_native_component
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) (a : A) :
    ((cocartesianIsoTransportDiagramComparison A).app a).val
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeIsoTransportObject l k p) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIsoTransportSectionComparison_native_component l k p a

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
