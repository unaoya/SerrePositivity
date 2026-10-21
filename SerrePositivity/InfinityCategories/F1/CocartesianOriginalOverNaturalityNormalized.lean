module

public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalOverNaturalitySecondImage

/-!
概要：元の over 自然性の三辺を同じ三端点へ揃え、指定像を回収する。
方針：証明済みの端点等式だけを既存の三辺に適用する。
規約：元の指定同型の値を変えない。
使われ方：充満忠実な後合成による三角等式の反映。
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

/-- 始点と共有頂点の表示だけを揃えた元の over 自然性。 -/
def cocartesianOriginalOverNaturalityNormalizedIso :
    FunctorIso (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q).sourceMap
      (cocartesianOriginalOverNaturalitySecondIso l k p q).sourceMap :=
  F2.functorIsoOfEq (cocartesianOriginalOverNaturalityIso l k p q)
    (cocartesianOriginalOverNaturality_source l k p q)
    (cocartesianOriginalOverNaturality_middle l k p q)

/-- 終点の表示だけを揃えた、同じ底上の制限をした大域自然性。 -/
def cocartesianOriginalOverNaturalityNormalizedSecondIso :
    FunctorIso (cocartesianOriginalOverNaturalitySecondIso l k p q).sourceMap
      (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q).targetMap :=
  F2.functorIsoOfEq (cocartesianOriginalOverNaturalitySecondIso l k p q) rfl
    (cocartesianOriginalOverNaturality_target l k p q)

/-- 表示だけを揃えた元の over 自然性の像は、既存の同じ指定合成を回収する。 -/
lemma cocartesianOriginalOverNaturalityNormalizedIso_postcomp_heq :
    HEq ((cocartesianOriginalOverNaturalityNormalizedIso l k p q).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q))
      (cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q) := by
  exact (functorIsoOfEq_postcomp_heq (cocartesianOriginalOverNaturalityIso l k p q)
    (cocartesianOriginalOverNaturality_source l k p q)
    (cocartesianOriginalOverNaturality_middle l k p q)
    (cocartesianBaseChangeHomCompositionNormalization l k p q)).trans
    ((cocartesianLocalHomComparison_overNaturalityIso_originalHom_postcomp_heq l k p q).trans
      (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_heq l k p q))

/-- 表示だけを揃えた同じ第二辺の像は、既存の指定第二辺を回収する。 -/
lemma cocartesianOriginalOverNaturalityNormalizedSecondIso_postcomp_heq :
    HEq ((cocartesianOriginalOverNaturalityNormalizedSecondIso l k p q).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q))
      ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
        (cocartesianBaseChangeHomRestrictionZero l k p q)) := by
  exact (functorIsoOfEq_postcomp_heq (cocartesianOriginalOverNaturalitySecondIso l k p q)
    rfl (cocartesianOriginalOverNaturality_target l k p q)
    (cocartesianBaseChangeHomCompositionNormalization l k p q)).trans
    (cocartesianOriginalOverNaturalitySecondIso_postcomp_heq l k p q)

end SerrePositivity.InfinityCategories
