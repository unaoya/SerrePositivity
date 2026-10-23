module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTransportTriangleIdentity
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomTransportTrianglePrecomposition

/-!
概要：既存の輸送結合同型の三角形は、元の全相対 Hom の同じ大域作用上で整合する。
方針：同じ比較三角形への元の作用で指定された三辺の等式を引き戻す。
規約：元の全 Hom・輸送結合同型・三辺の指定同型を保持する。
使われ方：共有頂点での元の大域分類 Hom 作用と局所自然性の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の同じ全 Hom 上で、指定された輸送三角形の三辺の合成の等式が成立する。 -/
lemma cocartesianBaseChangeHomTransport_compositionIso_originalHom_identity
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HomTransportTriangleCommutesAt
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
    (cocartesianBaseChangeHomTransport_compositionIso l k p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q) := by
  exact HomTransportTriangleCommutes.at_map _ _ _ _ _ _ _ _ _ _
    (cocartesianBaseChangeHomTransport_compositionIso_identity l k p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q)

end SerrePositivity.InfinityCategories
