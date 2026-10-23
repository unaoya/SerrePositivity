module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTransportTriangleDataCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondCompositeFactors
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondAssociativityNormalization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondFirstNormalization
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPastingTransport

/-!
概要：元の輸送三角形の第二辺は、既存の局所結合輸送と二回目の大域自然性の合成。
方針：元の分解三角形の二因子を同じ三端点に正規化して貼り合わせる。
規約：元の全 Hom 作用と全ての指定同型の値を保持する。
使われ方：共有頂点での大域自然性と局所自然性の三角形の等式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom 上で、第二辺の指定同型は既存の指定結合輸送と二回目の自然性の合成。 -/
lemma cocartesianBaseChangeTransportTriangleSecondIso_naturality_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq ((cocartesianBaseChangeTransportTriangleSecondIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q))
      (((cocartesianBaseChangeNativeHomTransportIso l k p q).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))).postcomp
                (cocartesianBaseChangeHomTransport l
                  ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
                  ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≪≫
        (cocartesianBaseChangeHomNaturalityIso l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)).precomp
            ((SSet.uliftFunctor.{u + 1, u}).map
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q))) := by
  have hpaste := functorIso_postcomp_precomp_trans_heq
    (cocartesianBaseChangeHomTransport l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianBaseChangeSecondTriangleHomComparison l k p q)
    (cocartesianBaseChangeSecondAssociativity_originalHom_source l k p q)
    (cocartesianBaseChangeSecondAssociativity_originalHom_target l k p q)
    (cocartesianBaseChangeSecondFirst_originalHom_target l k p q)
    (cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q)
    (cocartesianBaseChangeSecondTriangleHomFirstTransportIso l k p q) _ _
    (cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_postcomp_naturality_heq
      l k p q).symm
    (cocartesianBaseChangeSecondTriangleHomFirstTransportIso_naturality_heq l k p q).symm
  exact HEq.trans
    (cocartesianBaseChangeTransportTriangleSecondIso_precomp_heq l k p q _)
    ((cocartesianBaseChangeSecondHomCompositeTransportIso_originalHom_factors_heq l k p q).trans
      hpaste.symm)

end SerrePositivity.InfinityCategories
