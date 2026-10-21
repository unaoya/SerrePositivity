module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldPullbackHom

/-!
概要：部分底上の同じ universal scaffold 比較の二つの射影。
方針：定義された pullback の持ち上げの計算則を公開する。
規約：底と全空間の充填性は要求しない。
使われ方：指定辺保存条件を反映する同じ lift の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {E : SSet.{u}}
  (p : E ⟶ nerve C) (a : Over (nerve C))

/-- 同じ比較は部分底への第一射影を保つ。 -/
lemma cocartesianScaffoldPullbackOverMap_fst :
    (cocartesianScaffoldPullbackOverMap p a).left ≫ pullback.fst a.hom p =
      pullback.fst a.hom
        (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)) :=
  pullback.lift_fst _ _ _

/-- 同じ比較の第二射影は元の scaffold 比較との合成。 -/
lemma cocartesianScaffoldPullbackOverMap_snd :
    (cocartesianScaffoldPullbackOverMap p a).left ≫ pullback.snd a.hom p =
      pullback.snd a.hom
        (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)) ≫
          kanUniversalScaffold p :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
