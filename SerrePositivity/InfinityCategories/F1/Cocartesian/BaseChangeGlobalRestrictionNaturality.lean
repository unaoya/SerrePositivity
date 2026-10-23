module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalLocalTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalRestrictionCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorIsoSymmetricWhisker

/-!
概要：既存の局所制限自然性の第一因子を、元の全 Hom 上の二回目の大域自然性へ戻す。
方針：同じ一回目の底変換による前合成と後合成を交換する。
規約：元の全 Hom・指定された大域自然性とその制限を保持する。
使われ方：既存の局所制限自然性と三辺の第二因子の照合。
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

/-- 元の全 Hom に作用する同じ一回目の底変換。 -/
def cocartesianSingleBaseChangeHomAction :=
  (SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q)

/-- 元の全 Hom 上の二回目の大域自然性を、同じ底でさらに輸送した因子。 -/
def cocartesianBaseChangeGlobalSecondNaturalityPostIso :=
  (cocartesianBaseChangeGlobalSecondNaturalityFactorIso l k p q).postcomp
    (cocartesianBaseChangeRestrictedHomTransport l k p q)

/-- 指定自然性の前後合成の交換は、同じ両端の作用を回収する。 -/
lemma cocartesianBaseChangeGlobalRestrictionNaturality_endpoints :
    ((cocartesianIteratedLocalRestrictionNaturalityIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).sourceMap =
      (cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q).sourceMap ∧
    ((cocartesianIteratedLocalRestrictionNaturalityIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).targetMap =
      (cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q).targetMap := by
  exact FunctorIso.postcomp_precomp_endpoints
    (cocartesianBaseChangeHomNaturalityIso l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianBaseChangeRestrictedHomTransport l k p q)

/-- 元の全 Hom 上の同じ指定自然性は、既存の局所制限自然性の第一因子を回収する。 -/
lemma cocartesianBaseChangeGlobalRestrictionNaturality_heq :
    HEq (cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q)
      ((cocartesianIteratedLocalRestrictionNaturalityIso l k p q).precomp
        (cocartesianSingleBaseChangeHomAction k p q)) := by
  exact heq_of_eq (F2.functorIso_precomp_postcomp
    (cocartesianBaseChangeHomNaturalityIso l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianBaseChangeRestrictedHomTransport l k p q))

end SerrePositivity.InfinityCategories
