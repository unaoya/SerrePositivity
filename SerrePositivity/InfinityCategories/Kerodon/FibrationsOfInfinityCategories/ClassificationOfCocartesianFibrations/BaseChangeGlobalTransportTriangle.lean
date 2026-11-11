module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeGlobalTriangleEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportTriangleReindex

/-!
概要：元の大域輸送の三角形は、同じ指定された局所自然性因子の共通端点で可換。
方針：四端点と四つの指定値を同時に移して、元の三角等式を回収する。
規約：元の全 Hom・輸送結合同型・直接辺・第一辺・第二辺を保持する。
使われ方：元の局所自然性の三角等式を回収する貼り合わせ計算。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 同じ局所自然性因子の始点へ移した、元の指定輸送結合同型。 -/
def cocartesianBaseChangeGlobalTransportCompositionIso :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeOriginalGlobalCompositionIso l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTriangle_source l k p q) rfl

/-- 同じ第一辺の終点へ移した、元の指定直接辺。 -/
def cocartesianBaseChangeGlobalTransportDirectIso :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeOriginalGlobalDirectIso l k p q)
    rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTriangle_target l k p q)

/-- 元の大域輸送の三角形は、同じ指定四辺の共通端点で貼り合わせ等式を満たす。 -/
def CocartesianBaseChangeGlobalTransportTriangleCommutes : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareCommutes
    (cocartesianBaseChangeGlobalTransportCompositionIso l k p q)
    (cocartesianBaseChangeGlobalTransportDirectIso l k p q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSecondGlobalNaturalityIso l k p q).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeRestrictedHomTransport l k p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeFirstGlobalFactorIso l k p q)

/-- 元の全 Hom 上で、指定因子の同時正規化は元の輸送三角形の等式を回収する。 -/
lemma cocartesianBaseChangeGlobalTransportTriangleCommutes :
    CocartesianBaseChangeGlobalTransportTriangleCommutes l k p q := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportTriangleCommutesAt.reindex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomTransport_compositionIso_originalHom_identity l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTriangle_source l k p q) rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTriangle_middle l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTriangle_target l k p q) _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeTransportTriangleSecondIso_restriction_naturality_heq l k p q).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeFirstGlobalFactorIso_first_heq l k p q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
