module

public import SerrePositivity.InfinityCategories.F1.CocartesianLocalNativeRestrictionGlobalCoherence
public import SerrePositivity.InfinityCategories.F1.IsoTriangleIdentity

/-!
概要：元の全 Hom 上で回収した既存の局所自然性は、元の大域自然性の三角等式を満たす。
方針：同じ指定因子の三辺の等式を、端点をそろえた同じ二因子の合成へまとめる。
規約：元の全 Hom・局所自然性・大域自然性の指定値を保持する。
使われ方：底上の局所自然性と同じ元の大域分類作用の整合性。
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

/-- 元の全 Hom 上の既存の局所自然性は、元の大域自然性と同じ三角形を閉じる。 -/
def CocartesianGlobalNativeRestrictionTriangleCommutes : Prop :=
  IsoTriangleCommutes
    (cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
    (cocartesianBaseChangeGlobalTransportDirectIso l k p q)

/-- 同じ指定二因子をまとめた局所自然性の三角等式を回収する。 -/
lemma cocartesianGlobalNativeRestrictionTriangleCommutes :
    CocartesianGlobalNativeRestrictionTriangleCommutes l k p q := by
  have h₀ : IsoLocalTriangleCommutes
      (cocartesianBaseChangeGlobalNativeComparisonIso l k p q)
      (cocartesianBaseChangeGlobalRestrictionComparisonIso l k p q)
      ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
        (cocartesianBaseChangeHomRestrictionZero l k p q))
      (cocartesianBaseChangeGlobalTransportDirectIso l k p q) := by
    exact cocartesianBaseChangeGlobalLocalTriangleCommutes l k p q
  have h₁ := IsoLocalTriangleCommutes.replace_second h₀
    (cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso l k p q)
    (F2.functorIsoOfEq_heq _ _ _)
  exact IsoLocalTriangleCommutes.merge h₁

end SerrePositivity.InfinityCategories
