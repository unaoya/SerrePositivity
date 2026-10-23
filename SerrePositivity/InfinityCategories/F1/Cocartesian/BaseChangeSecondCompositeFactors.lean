module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondCompositeNaturality

/-!
概要：元の第二面の分解比較は、同じ結合比較と二回目の底変換の指定因子の合成。
方針：既存の合成同型の端点正規化を取り除き、同じ作用で前合成する。
規約：元の両因子の指定値を保持する。
使われ方：第二面の同型を元の大域自然性と局所結合自然性に照合する。
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

/-- 指定された元の分解比較は、任意の同じ作用で引き戻すと二つの指定因子の合成。 -/
lemma cocartesianBaseChangeSecondTriangleHomCompositeTransportIso_precomp_factors_heq
    {K : SSet.{u + 1}} (r : K ⟶ cocartesianBaseChangeSecondTriangleHomSpace l k p q) :
    HEq ((cocartesianBaseChangeSecondTriangleHomCompositeTransportIso l k p q).precomp r)
      ((((cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q).postcomp
        (cocartesianBaseChangeHomTransport l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))).precomp r) ≪≫
        (cocartesianBaseChangeSecondTriangleHomFirstTransportIso l k p q).precomp r) := by
  have h := functorIsoOfEq_precomp_heq
    ((cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q).postcomp
      (cocartesianBaseChangeHomTransport l
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≪≫
      cocartesianBaseChangeSecondTriangleHomFirstTransportIso l k p q)
    (Category.assoc _ _ _) rfl r
  exact h.trans (heq_of_eq (F2.functorIso_precomp_trans _ _ r))

/-- 同じ元の全 Hom 作用上で、第二面の指定比較は同じ二因子の合成そのもの。 -/
lemma cocartesianBaseChangeSecondHomCompositeTransportIso_originalHom_factors_heq :
    HEq ((cocartesianBaseChangeSecondHomCompositeTransportIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q ≫
        cocartesianBaseChangeTriangleHomSecond l k p q))
      ((((cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q).postcomp
        (cocartesianBaseChangeHomTransport l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))).precomp
            (cocartesianBaseChangeSecondTriangleHomComparison l k p q)) ≪≫
        (cocartesianBaseChangeSecondTriangleHomFirstTransportIso l k p q).precomp
          (cocartesianBaseChangeSecondTriangleHomComparison l k p q)) := by
  exact (cocartesianBaseChangeSecondHomCompositeTransportIso_naturality_heq l k p q).trans
    (cocartesianBaseChangeSecondTriangleHomCompositeTransportIso_precomp_factors_heq
      l k p q (cocartesianBaseChangeSecondTriangleHomComparison l k p q))

end SerrePositivity.InfinityCategories
