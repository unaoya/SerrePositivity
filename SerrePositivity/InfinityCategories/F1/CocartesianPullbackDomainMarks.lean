module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackEdgeCover

/-!
概要：底の図式の引き戻しに、各底変換の元の cocartesian 辺を指定する。
方針：第一射影に関する辺を指定し、固定した全空間への射影で保存と被覆を確認する。
規約：合成した射影の辺へ置き換えず、各底変換に固有の cocartesian 辺を使う。
使われ方：元の cocartesian Hom の指定辺を保つ降下定理の実際の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 各引き戻しに指定する辺は、その可変の底への射影に関する cocartesian 辺。 -/
def cocartesianPullbackDomainMark {J : Type v} [Category.{w} J]
    {E B : SSet.{u}} (p : E ⟶ B) (D : J ⥤ Over B) (j : J) :
    Set (((cocartesianPullbackDomainDiagram p D).obj j).left _⦋1⦌) :=
  {e | IsCocartesianEdge (pullback.fst (D.obj j).hom p) e}

/-- 底の図式の各誘導射は、各底変換に固有の指定辺を保つ。 -/
lemma cocartesianPullbackDomainMark_map {J : Type v} [Category.{w} J]
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (D : J ⥤ Over B) {j k : J} (f : j ⟶ k)
    (e : ((cocartesianPullbackDomainDiagram p D).obj j).left _⦋1⦌)
    (he : e ∈ cocartesianPullbackDomainMark p D j) :
    ((cocartesianPullbackDomainDiagram p D).map f).left.app (Opposite.op ⦋1⦌) e ∈
      cocartesianPullbackDomainMark p D k :=
  isCocartesianEdge_overPullback_map p (D.map f) e he

/-- 元の全空間への余錐の各脚は、各底変換の指定辺を元の cocartesian 辺へ送る。 -/
lemma cocartesianPullbackDomainMark_cocone {J : Type v} [Category.{w} J]
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (D : J ⥤ Over B) (j : J)
    (e : ((cocartesianPullbackDomainDiagram p D).obj j).left _⦋1⦌)
    (he : e ∈ cocartesianPullbackDomainMark p D j) :
    IsCocartesianEdge p
      (((cocartesianPullbackDomainCocone p D).ι.app j).left.app (Opposite.op ⦋1⦌) e) :=
  (isCocartesianEdge_overPullback_iff p (D.obj j) e).mp he

/-- 底を覆う余極限の各項の指定辺は、元の全 cocartesian 辺を覆う。 -/
lemma cocartesianPullbackDomainMark_cover {J : Type v} [Category.{w} J] [Small.{u} J]
    {E B : SSet.{u}} (p : E ⟶ B) (D : J ⥤ Over B)
    (hc : IsColimit ((Over.forgetCocone B).whisker D))
    (e : E _⦋1⦌) (he : IsCocartesianEdge p e) :
    ∃ j t, t ∈ cocartesianPullbackDomainMark p D j ∧
      ((cocartesianPullbackDomainCocone p D).ι.app j).left.app (Opposite.op ⦋1⦌) t = e :=
  exists_cocartesianPullbackEdge_of_base_colimit p D hc e he

end SerrePositivity.InfinityCategories
