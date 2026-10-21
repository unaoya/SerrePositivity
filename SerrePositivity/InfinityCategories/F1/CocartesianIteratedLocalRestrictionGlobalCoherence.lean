module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeGlobalRestrictionInverse

/-!
概要：既存の局所制限自然性を元の全 Hom に戻すと、導出した三辺の第二因子そのもの。
方針：同じ一回目の底変換と三端点の回収で、元の二因子の指定値を貼り合わせる。
規約：既存の局所制限自然性・指定因子・元の全 Hom 作用を保持する。
使われ方：元の三辺の等式を既存の局所自然性の指定値へ移す。
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

/-- 元の全 Hom 上の局所制限自然性を表す、同じ指定二因子の合成。 -/
def cocartesianBaseChangeGlobalRestrictionComparisonIso :
    FunctorIso (cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q).sourceMap
      (cocartesianBaseChangeGlobalRestrictionInverseIso l k p q).targetMap :=
  cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q ≪≫
    cocartesianBaseChangeGlobalRestrictionInverseIso l k p q

/-- 既存の局所制限自然性の前合成は、同じ元の全 Hom 上の指定二因子の合成に一致。 -/
lemma cocartesianIteratedLocalHomComparison_restrictionIso_originalHom_heq :
    HEq ((cocartesianIteratedLocalHomComparison_restrictionIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q))
      (cocartesianBaseChangeGlobalRestrictionComparisonIso l k p q) := by
  have h₁ := functorIsoOfEq_precomp_heq
    (cocartesianIteratedLocalRestrictionCompositeIso l k p q)
    (cocartesianIteratedLocalRestrictionComposite_source l k p q)
    (cocartesianIteratedLocalRestrictionComposite_target l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
  have h₂ := functorIso_precomp_paste_heq
    (cocartesianIteratedLocalRestrictionNaturalityIso l k p q)
    (cocartesianIteratedLocalRestrictionNormalizedInverseIso l k p q)
    (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q)
    (cocartesianBaseChangeGlobalRestrictionInverseIso l k p q)
    (cocartesianBaseChangeGlobalRestrictionNaturality_endpoints l k p q).1
    (cocartesianBaseChangeGlobalRestrictionNaturality_endpoints l k p q).2
    (cocartesianBaseChangeGlobalRestrictionInverse_target l k p q)
    (cocartesianBaseChangeGlobalRestrictionNaturality_heq l k p q)
    (cocartesianBaseChangeGlobalRestrictionInverse_heq l k p q)
  exact HEq.trans h₁ h₂

end SerrePositivity.InfinityCategories
