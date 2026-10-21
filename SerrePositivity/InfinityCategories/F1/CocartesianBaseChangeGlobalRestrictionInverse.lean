module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeGlobalRestrictionNaturality

/-!
概要：既存の局所制限自然性の逆因子を、元の全 Hom 上の指定制限自然性の逆へ戻す。
方針：同じ二段の前合成・逆同型・始点正規化の交換を使う。
規約：元の全 Hom・指定制限自然性とその逆の値を保持する。
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

/-- 元の全 Hom 上で始点をそろえた、同じ指定制限自然性の逆。 -/
def cocartesianBaseChangeGlobalRestrictionInverseIso :
    FunctorIso (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).targetMap
      (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap :=
  (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).symm

/-- 元の二段の前合成をした逆因子は、同じ指定逆自然性の終点作用を回収する。 -/
lemma cocartesianBaseChangeGlobalRestrictionInverse_target :
    ((cocartesianIteratedLocalRestrictionNormalizedInverseIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).targetMap =
    (cocartesianBaseChangeGlobalRestrictionInverseIso l k p q).targetMap := by
  exact functorIso_normalized_symm_precomp_precomp_target
    (cocartesianBaseChangeHomTransport_restrictionIso l k p q)
    (cocartesianStraighteningHomInterval
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianIteratedLocalRestrictionInverse_source l k p q)
    (cocartesianBaseChangeFirstGlobalRestriction_source l k p q)

/-- 同じ二段の前合成と始点正規化は、指定制限自然性の逆を回収する。 -/
lemma cocartesianBaseChangeGlobalRestrictionInverse_heq :
    HEq (cocartesianBaseChangeGlobalRestrictionInverseIso l k p q)
      ((cocartesianIteratedLocalRestrictionNormalizedInverseIso l k p q).precomp
        (cocartesianSingleBaseChangeHomAction k p q)) := by
  exact (functorIso_normalized_symm_precomp_precomp_heq
    (cocartesianBaseChangeHomTransport_restrictionIso l k p q)
    (cocartesianStraighteningHomInterval
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianIteratedLocalRestrictionInverse_source l k p q)
    (cocartesianBaseChangeFirstGlobalRestriction_source l k p q)).symm

end SerrePositivity.InfinityCategories
