module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalHomOverNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulNormalizedIsoRecovery
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalRestrictionNaturality

/-!
概要：底上の指定自然性は正規化後に元の局所自然性そのものを回収する。
方針：同じ充満忠実な逆像の回収則を全 Hom の前合成にも適用する。
規約：同じ元の全 Hom と指定同型を保持する。
使われ方：共有頂点の三角等式の移送。
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

/-- 底上の指定自然性の像は、既存の指定局所自然性。 -/
lemma cocartesianLocalHomComparison_overNaturalityIso_postcomp_heq :
    HEq ((cocartesianLocalHomComparison_overNaturalityIso l k p q).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q))
      (cocartesianLocalHomComparison_nativeRestrictionIso l k p q) := by
  exact (cocartesianLocalHomOverNormalization_isFullyFaithful l k p q).preimageNormalizedFunctorIso_postcomp_heq
      (cocartesianLocalHomOverNaturalitySource l k p q)
      (cocartesianLocalHomOverNaturalityTarget l k p q)
      (cocartesianLocalHomComparison_nativeRestrictionIso l k p q) rfl
      (cocartesianLocalHomOverNaturalityTarget_normalization l k p q)

/-- 元の全 Hom 上でも正規化後に同じ指定局所自然性を回収する。 -/
lemma cocartesianLocalHomComparison_overNaturalityIso_originalHom_postcomp_heq :
    HEq (((cocartesianLocalHomComparison_overNaturalityIso l k p q).precomp
      (cocartesianSingleBaseChangeHomAction k p q)).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q))
      ((cocartesianLocalHomComparison_nativeRestrictionIso l k p q).precomp
        (cocartesianSingleBaseChangeHomAction k p q)) := by
  exact (cocartesianLocalHomOverNormalization_isFullyFaithful l k p q).preimageNormalizedFunctorIso_precomp_postcomp_heq
      (cocartesianLocalHomOverNaturalitySource l k p q)
      (cocartesianLocalHomOverNaturalityTarget l k p q)
      (cocartesianLocalHomComparison_nativeRestrictionIso l k p q) rfl
      (cocartesianLocalHomOverNaturalityTarget_normalization l k p q)
      (cocartesianSingleBaseChangeHomAction k p q)

end SerrePositivity.InfinityCategories
