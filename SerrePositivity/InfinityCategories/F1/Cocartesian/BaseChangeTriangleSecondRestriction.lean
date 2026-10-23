module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleSecondEndpoints
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleSecondNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoPrecompositionProjection
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalSecondFactors

/-!
概要：第二辺をさらに制限した指定値は、既存の結合比較と二回目の大域自然性の制限。
方針：元の全 Hom 上の両端の回収と、指定値の前後合成の交換を使う。
規約：元の第二辺・指定結合輸送・二回目の大域自然性を保持する。
使われ方：元の輸送三角形の同じ三辺を局所自然性の貼り合わせへ移す。
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

/-- 元の全 Hom 上の指定結合輸送と、二回目の大域自然性の指定合成。 -/
def cocartesianBaseChangeSecondGlobalNaturalityIso :
    FunctorIso
      ((((SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ≫
        (((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
          cocartesianStraighteningHomInterval
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q)) ≫
          cocartesianBaseChangeAssociativityHomTransport l k p q)) ≫
        cocartesianBaseChangeHomTransport l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
      (((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
        cocartesianBaseChangeHomRestrictionOne l k p q) :=
  cocartesianBaseChangeGlobalNativeTransportFactorIso l k p q ≪≫
    cocartesianBaseChangeGlobalSecondNaturalityFactorIso l k p q

/-- 元の三角形の同じ第二辺を制限しても、二つの指定因子の合成を保持する。 -/
lemma cocartesianBaseChangeTransportTriangleSecondIso_restriction_naturality_heq :
    HEq (((cocartesianBaseChangeTransportTriangleSecondIso l k p q).postcomp
      (cocartesianBaseChangeRestrictedHomTransport l k p q)).precomp
        (cocartesianBaseChangeTriangleHomComparison l k p q))
      ((cocartesianBaseChangeSecondGlobalNaturalityIso l k p q).postcomp
        (cocartesianBaseChangeRestrictedHomTransport l k p q)) := by
  exact functorIso_postcomp_precomp_of_heq
    (cocartesianBaseChangeTransportTriangleSecondIso l k p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q)
    (cocartesianBaseChangeTriangleSecond_originalHom_source l k p q)
    (cocartesianBaseChangeTriangleSecond_originalHom_target l k p q)
    (cocartesianBaseChangeSecondGlobalNaturalityIso l k p q)
    (cocartesianBaseChangeTransportTriangleSecondIso_naturality_heq l k p q).symm
    (cocartesianBaseChangeRestrictedHomTransport l k p q)

end SerrePositivity.InfinityCategories
