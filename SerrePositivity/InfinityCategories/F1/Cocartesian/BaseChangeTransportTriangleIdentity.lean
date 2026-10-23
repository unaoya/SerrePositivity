module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransportComposition

/-!
概要：元の底変換 Hom 輸送の結合同型が、同じ共通 Hom 上の指定三辺を回収する。
方針：前合成で降ろした既存の同型の回収則を実際の比較三角形に適用する。
規約：元の輸送・切断・比較同型を保持する。
使われ方：大域分類作用の共有頂点での整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の結合輸送比較は、共通 Hom 上で指定された三辺の三角恒等式を満たす。 -/
lemma cocartesianBaseChangeHomTransport_compositionIso_identity
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HomTransportTriangleCommutes
    (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)
    (cocartesianBaseChangeRestrictedHomTransport l k p q)
    (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
          cocartesianBaseChangeHomTransport l
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianBaseChangeHomTransport (l ⋙ k) p q ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q)
    (cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso l k p q)
    (cocartesianBaseChangeTransportTriangleSecondIso l k p q)
    (cocartesianBaseChangeTransportTriangleDirectIso l k p q)
    (cocartesianBaseChangeHomTransport_compositionIso l k p q) := by
  exact homTransportTriangleCoherence_identity
    (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)
    (cocartesianBaseChangeRestrictedHomTransport l k p q)
    (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
          cocartesianBaseChangeHomTransport l
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianBaseChangeHomTransport (l ⋙ k) p q ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q)
    (cocartesianBaseChangeTriangleHomLong_one_isQCatEquivalence l k p q)
    (cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso l k p q)
    (cocartesianBaseChangeTransportTriangleSecondIso l k p q)
    (cocartesianBaseChangeTransportTriangleDirectIso l k p q)

end SerrePositivity.InfinityCategories
