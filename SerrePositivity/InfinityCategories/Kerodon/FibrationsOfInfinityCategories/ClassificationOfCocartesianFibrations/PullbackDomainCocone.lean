module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OverPullbackEdges

/-!
概要：底を覆う図式の全ての引き戻しを、元の全空間を頂点とする底上の余錐へ束ねる。
方針：標準の Over.pullback と Over.map を使い、次数ごとの pullback の余極限保存を適用する。
規約：余錐の頂点は元の射影そのものであり、同型な別の全空間へ置き換えない。
使われ方：セルへの引き戻しの cocartesian Hom の降下の元の全空間側の入力。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 各底上の対象の引き戻しを、元の底への射影を持つ対象として束ねる。 -/
def cocartesianPullbackDomainDiagram {J : Type v} [Category.{w} J]
    {E B : SSet.{u}} (p : E ⟶ B) (D : J ⥤ Over B) : J ⥤ Over B :=
  D ⋙ Over.pullback p ⋙ Over.map p

/-- 各引き戻しの第二射影は、元の全空間を頂点とする底上の余錐をなす。 -/
def cocartesianPullbackDomainCocone {J : Type v} [Category.{w} J]
    {E B : SSet.{u}} (p : E ⟶ B) (D : J ⥤ Over B) :
    Cocone (cocartesianPullbackDomainDiagram p D) where
  pt := Over.mk p
  ι :=
    { app j := Over.homMk (pullback.snd (D.obj j).hom p) rfl
      naturality {j k} f := by
        apply Over.OverMorphism.ext
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd p (D.map f) }

/-- 底を覆う元の余極限の引き戻しは、元の全空間を厳密な余極限として回収する。 -/
def cocartesianPullbackDomainCocone_isColimit {J : Type v} [Category.{w} J] [Small.{u} J]
    {E B : SSet.{u}} (p : E ⟶ B) (D : J ⥤ Over B)
    (hc : IsColimit ((Over.forgetCocone B).whisker D)) :
    IsColimit ((Over.forget B).mapCocone (cocartesianPullbackDomainCocone p D)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.sset_isColimit_of_pullback ((Over.forgetCocone B).whisker D) hc
    ((Over.forget B).mapCocone (cocartesianPullbackDomainCocone p D))
    (Functor.whiskerLeft D (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackProjection p)) p
    (fun j ↦ (IsPullback.of_hasPullback (D.obj j).hom p).flip)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
