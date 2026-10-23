module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondHomDecompositionEndpoints
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondTriangleHomTransport
public import SerrePositivity.InfinityCategories.F1.FunctorIsoEndpointProjection

/-!
概要：元の第二面の輸送を降ろす前の同じ指定同型を、元の長辺射影で型付けする。
方針：分解三角形の両端の厳密な等式で端点だけを正規化する。
規約：既存の結合比較と二回目の輸送の合成同型を保持する。
使われ方：同じ前合成の充満忠実性による逆像の回収則。
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

/-- 第二面の同じ輸送を降ろす前の、元の長辺射影に沿う指定同型。 -/
def cocartesianBaseChangeSecondHomCompositeLiftIso :
    FunctorIso
      (cocartesianBaseChangeSecondTriangleHomLong l k p q ≫
        (cocartesianBaseChangeSecondHomSpanOne l k p q ≫
          (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
            cocartesianBaseChangeHomTransport l
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))))
      (cocartesianBaseChangeSecondTriangleHomLong l k p q ≫
        cocartesianBaseChangeSecondHomSpanZero l k p q) :=
  F2.functorIsoOfEq (cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q)
    (by rw [← cocartesianBaseChangeSecondHomDecomposition_one, Category.assoc])
    (cocartesianBaseChangeSecondHomDecomposition_zero l k p q).symm

/-- 元の指定同型の端点正規化は、同じ合成同型の値を保持する。 -/
lemma cocartesianBaseChangeSecondHomCompositeLiftIso_heq :
    HEq (cocartesianBaseChangeSecondHomCompositeLiftIso l k p q)
      (cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q) := by
  exact F2.functorIsoOfEq_heq
    (cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q)
    (by rw [← cocartesianBaseChangeSecondHomDecomposition_one, Category.assoc])
    (cocartesianBaseChangeSecondHomDecomposition_zero l k p q).symm

/-- 同じ指定合成同型の端点正規化は、任意の元の作用で前合成した後も値を保持する。 -/
lemma cocartesianBaseChangeSecondHomCompositeLiftIso_precomp_heq
    {K : SSet.{u + 1}} (r : K ⟶ cocartesianBaseChangeSecondTriangleHomSpace l k p q) :
    HEq ((cocartesianBaseChangeSecondHomCompositeLiftIso l k p q).precomp r)
      ((cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q).precomp r) := by
  exact functorIsoOfEq_precomp_heq
    (cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q)
    (by rw [← cocartesianBaseChangeSecondHomDecomposition_one, Category.assoc])
    (cocartesianBaseChangeSecondHomDecomposition_zero l k p q).symm r

end SerrePositivity.InfinityCategories
