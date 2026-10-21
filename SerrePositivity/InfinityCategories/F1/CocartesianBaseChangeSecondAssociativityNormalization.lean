module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondAssociativityEndpoints
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionProjection

/-!
概要：元の第二面の結合因子を、二重底変換と既存の局所輸送の同じ端点へ正規化する。
方針：元の全 Hom 上の両端の厳密な等式と指定値の一致を使う。
規約：同じ結合因子と既存の局所輸送を保持する。
使われ方：第二面の指定比較を既存の二因子の合成として貼り合わせる。
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

/-- 同じ端点に正規化した結合因子は、元の二重底変換による既存の局所輸送の前合成。 -/
lemma cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_normalized :
    F2.functorIsoOfEq
      ((cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q).precomp
        (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      (cocartesianBaseChangeSecondAssociativity_originalHom_source l k p q)
      (cocartesianBaseChangeSecondAssociativity_originalHom_target l k p q) =
    (cocartesianBaseChangeNativeHomTransportIso l k p q).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    (cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_doubleBaseChange_heq l k p q))

/-- 同じ結合因子に二回目の輸送を後合成しても、既存の指定局所輸送の値を保持する。 -/
lemma cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_postcomp_naturality_heq :
    HEq (((cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q).postcomp
      (cocartesianBaseChangeHomTransport l
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))).precomp
          (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      (((cocartesianBaseChangeNativeHomTransportIso l k p q).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))).postcomp
                (cocartesianBaseChangeHomTransport l
                  ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
                  ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) := by
  exact functorIsoOfEq_precomp_postcomp_heq_of_eq
    (cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q)
    (cocartesianBaseChangeSecondTriangleHomComparison l k p q)
    (cocartesianBaseChangeSecondAssociativity_originalHom_source l k p q)
    (cocartesianBaseChangeSecondAssociativity_originalHom_target l k p q)
    _ (cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_normalized l k p q) _

end SerrePositivity.InfinityCategories
