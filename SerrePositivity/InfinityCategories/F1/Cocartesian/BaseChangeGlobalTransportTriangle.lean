module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalTriangleEndpoints
public import SerrePositivity.InfinityCategories.F1.HomTransportTriangleReindex

/-!
概要：元の大域輸送の三角形は、同じ指定された局所自然性因子の共通端点で可換。
方針：四端点と四つの指定値を同時に移して、元の三角等式を回収する。
規約：元の全 Hom・輸送結合同型・直接辺・第一辺・第二辺を保持する。
使われ方：元の局所自然性の三角等式を回収する貼り合わせ計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ局所自然性因子の始点へ移した、元の指定輸送結合同型。 -/
def cocartesianBaseChangeGlobalTransportCompositionIso :=
  F2.functorIsoOfEq (cocartesianBaseChangeOriginalGlobalCompositionIso l k p q)
    (cocartesianBaseChangeGlobalTriangle_source l k p q) rfl

/-- 同じ第一辺の終点へ移した、元の指定直接辺。 -/
def cocartesianBaseChangeGlobalTransportDirectIso :=
  F2.functorIsoOfEq (cocartesianBaseChangeOriginalGlobalDirectIso l k p q)
    rfl (cocartesianBaseChangeGlobalTriangle_target l k p q)

/-- 元の大域輸送の三角形は、同じ指定四辺の共通端点で貼り合わせ等式を満たす。 -/
def CocartesianBaseChangeGlobalTransportTriangleCommutes : Prop :=
  FunctorIsoSquareCommutes
    (cocartesianBaseChangeGlobalTransportCompositionIso l k p q)
    (cocartesianBaseChangeGlobalTransportDirectIso l k p q)
    ((cocartesianBaseChangeSecondGlobalNaturalityIso l k p q).postcomp
      (cocartesianBaseChangeRestrictedHomTransport l k p q))
    (cocartesianBaseChangeFirstGlobalFactorIso l k p q)

/-- 元の全 Hom 上で、指定因子の同時正規化は元の輸送三角形の等式を回収する。 -/
lemma cocartesianBaseChangeGlobalTransportTriangleCommutes :
    CocartesianBaseChangeGlobalTransportTriangleCommutes l k p q := by
  exact HomTransportTriangleCommutesAt.reindex
    (cocartesianBaseChangeHomTransport_compositionIso_originalHom_identity l k p q)
    (cocartesianBaseChangeGlobalTriangle_source l k p q) rfl
    (cocartesianBaseChangeGlobalTriangle_middle l k p q)
    (cocartesianBaseChangeGlobalTriangle_target l k p q) _ _ _ _
    (F2.functorIsoOfEq_heq _ _ _) (F2.functorIsoOfEq_heq _ _ _)
    (cocartesianBaseChangeTransportTriangleSecondIso_restriction_naturality_heq l k p q).symm
    (cocartesianBaseChangeFirstGlobalFactorIso_first_heq l k p q)

end SerrePositivity.InfinityCategories
