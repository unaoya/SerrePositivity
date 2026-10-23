module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondHomCompositeTransport
public import SerrePositivity.InfinityCategories.F1.HomTransportTriangleIdentity
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionProjection

/-!
概要：第二面の元の輸送同型を分解三角形へ戻すと、元の指定合成同型を回収する。
方針：同値による前合成の充満忠実性の逆像の像を計算する。
規約：既存の第二面の輸送と分解三角形を保持する。
使われ方：第二面の同型を元の大域 Hom 作用上で照合する。
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

/-- 第二面の同じ逆像を前合成すると、元の端点正規化された合成同型そのものへ戻る。 -/
lemma cocartesianBaseChangeSecondHomCompositeTransportIso_projection :
    (cocartesianBaseChangeSecondHomCompositeTransportIso l k p q).precomp
        (cocartesianBaseChangeSecondTriangleHomLong l k p q) =
      cocartesianBaseChangeSecondHomCompositeLiftIso l k p q := by
  exact IsQCatEquivalence.preimage_precompFunctorIso
    (cocartesianBaseChangeSecondTriangleHomLong_isQCatEquivalence l k p q)
    (F := cocartesianBaseChangeSecondHomSpanOne l k p q ≫
      (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
        cocartesianBaseChangeHomTransport l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
    (G := cocartesianBaseChangeSecondHomSpanZero l k p q)
    (cocartesianBaseChangeSecondHomCompositeLiftIso l k p q)

/-- 第二面の元の比較は、分解三角形に戻すと同じ指定合成同型の値を回収する。 -/
lemma cocartesianBaseChangeSecondHomCompositeTransportIso_projection_heq :
    HEq ((cocartesianBaseChangeSecondHomCompositeTransportIso l k p q).precomp
      (cocartesianBaseChangeSecondTriangleHomLong l k p q))
      (cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q) := by
  exact HEq.trans
    (heq_of_eq (cocartesianBaseChangeSecondHomCompositeTransportIso_projection l k p q))
    (cocartesianBaseChangeSecondHomCompositeLiftIso_heq l k p q)

/-- 任意の元の作用から分解三角形へ進んだ後も、同じ指定同型を回収する。 -/
lemma cocartesianBaseChangeSecondHomCompositeTransportIso_projection_precomp_heq
    {K : SSet.{u + 1}} (r : K ⟶ cocartesianBaseChangeSecondTriangleHomSpace l k p q) :
    HEq ((cocartesianBaseChangeSecondHomCompositeTransportIso l k p q).precomp
      (r ≫ cocartesianBaseChangeSecondTriangleHomLong l k p q))
      ((cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q).precomp r) := by
  exact functorIso_precomp_of_projection_heq
    (cocartesianBaseChangeSecondHomCompositeTransportIso l k p q)
    (cocartesianBaseChangeSecondTriangleHomLong l k p q)
    (cocartesianBaseChangeSecondHomCompositeLiftIso l k p q)
    (cocartesianBaseChangeSecondHomCompositeTransportIso_projection l k p q)
    (cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q) r
    (cocartesianBaseChangeSecondHomCompositeLiftIso_precomp_heq l k p q r)

end SerrePositivity.InfinityCategories
