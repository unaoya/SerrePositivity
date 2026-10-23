module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTransportTriangleData
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionProjection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の輸送三角形の第二辺・直接辺は、既存の指定同型の端点正規化そのもの。
方針：同じ元の作用で前合成し、端点正規化を保って同じ指定値を回収する。
規約：元の三角形・第二面・長辺の比較同型を保持する。
使われ方：元の大域三角形の等式を既存の局所自然性の等式へ移す。
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

/-- 同じ第二辺は、前合成後も元の第二面の指定比較の値を回収する。 -/
lemma cocartesianBaseChangeTransportTriangleSecondIso_precomp_heq
    {K : SSet.{u + 1}} (r : K ⟶ cocartesianBaseChangeTriangleHomSpace l k p q) :
    HEq ((cocartesianBaseChangeTransportTriangleSecondIso l k p q).precomp r)
      ((cocartesianBaseChangeSecondHomCompositeTransportIso l k p q).precomp
        (r ≫ cocartesianBaseChangeTriangleHomSecond l k p q)) := by
  exact functorIsoOfEq_precomp_precomp_heq
    (cocartesianBaseChangeSecondHomCompositeTransportIso l k p q)
    (cocartesianBaseChangeTriangleHomSecond l k p q)
    (by rw [← Category.assoc, ← cocartesianBaseChangeTriangleHom_second_one l k p q])
    (cocartesianBaseChangeTriangleHom_middle l k p q).symm r

/-- 同じ直接辺は、前合成後も元の長辺の比較と表示正規化の同じ合成。 -/
lemma cocartesianBaseChangeTransportTriangleDirectIso_precomp_heq
    {K : SSet.{u + 1}} (r : K ⟶ cocartesianBaseChangeTriangleHomSpace l k p q) :
    HEq ((cocartesianBaseChangeTransportTriangleDirectIso l k p q).precomp r)
      (((cocartesianBaseChangeTriangleHomLong_transportIso l k p q).precomp r).postcomp
        (cocartesianBaseChangeHomCompositionNormalization l k p q)) := by
  exact functorIsoOfEq_postcomp_precomp_heq
    (cocartesianBaseChangeTriangleHomLong_transportIso l k p q)
    (cocartesianBaseChangeHomCompositionNormalization l k p q)
    (Category.assoc _ _ _)
    (cocartesianBaseChangeTriangleHom_zero_normalization l k p q) r

end SerrePositivity.InfinityCategories
