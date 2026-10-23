module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNaturalityFactorCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeFirstRestrictionFactor
public import SerrePositivity.InfinityCategories.F1.FunctorIsoEndpointProjection

/-!
概要：元の制限正方形の源の指定因子比較を、元の大域自然性と同じ端点へ移す。
方針：元の span の両射影が回収する作用を使い、同じ指定値を正規化する。
規約：元の全 Hom 作用と指定切断・指定自然性を保持する。
使われ方：第一辺の制限正方形を局所自然性の三角等式へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom 上の指定 span の因子比較。 -/
def cocartesianBaseChangeGlobalFactorIso :=
  homSpanSectionTransportFactorIso
    (cocartesianBaseChangeHomSpanOne k p q) (cocartesianBaseChangeHomSpanZero k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeHomComparison k p q)

/-- 元の因子比較の始点は同じ底変換の分類作用と指定輸送の合成。 -/
lemma cocartesianBaseChangeGlobalFactor_source :
    ((cocartesianBaseChangeHomComparison k p q ≫
      cocartesianBaseChangeHomSpanOne k p q) ≫ cocartesianBaseChangeHomTransport k p q) =
    (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
          cocartesianBaseChangeHomTransport k p q := by
  rw [cocartesianBaseChangeHomComparison_one]
  exact Category.assoc _ _ _

/-- 同じ因子比較を正規化すると、元の大域自然性そのものを回収する。 -/
lemma cocartesianBaseChangeGlobalFactorIso_normalized :
    F2.functorIsoOfEq (cocartesianBaseChangeGlobalFactorIso k p q)
      (cocartesianBaseChangeGlobalFactor_source k p q)
      (cocartesianBaseChangeHomComparison_zero k p q) =
    cocartesianBaseChangeHomNaturalityIso k p q := by
  exact eq_of_heq (HEq.trans (F2.functorIsoOfEq_heq _ _ _)
    (cocartesianBaseChangeHomNaturalityIso_factor_heq k p q).symm)

/-- 元の制限後も、正規化した源の因子比較は同じ大域自然性の指定値を保持する。 -/
lemma cocartesianBaseChangeGlobalFactorIso_restriction_heq
    {A : Type u} [Category.{u} A] (l : A ⥤ D) :
    HEq ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
      ((cocartesianBaseChangeGlobalFactorIso k p q).postcomp
        (cocartesianBaseChangeHomRestrictionZero l k p q)) := by
  exact functorIsoOfEq_postcomp_heq_of_eq
    (cocartesianBaseChangeGlobalFactorIso k p q)
    (cocartesianBaseChangeGlobalFactor_source k p q)
    (cocartesianBaseChangeHomComparison_zero k p q)
    (cocartesianBaseChangeHomNaturalityIso k p q)
    (cocartesianBaseChangeGlobalFactorIso_normalized k p q)
    (cocartesianBaseChangeHomRestrictionZero l k p q)

end SerrePositivity.InfinityCategories
