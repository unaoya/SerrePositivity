module

public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalOverNaturalityNormalized
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulTriangleReflection

/-!
概要：元の over 自然性自身は、元の大域自然性との三角等式を満たす。
方針：三端点と三つの指定像を揃え、充満忠実な正規化で等式を反映する。
規約：元の全 Hom と既存の指定三辺を保持する。
使われ方：共有セルでの成分 path の整合と二単体の分類 Hom 比較。
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

/-- 端点の表示だけを揃えた既存の over 自然性と元の大域自然性との三角等式。 -/
def CocartesianOriginalOverNaturalityTriangleCommutes : Prop :=
  IsoTriangleCommutes (cocartesianOriginalOverNaturalityNormalizedIso l k p q)
    (cocartesianOriginalOverNaturalityNormalizedSecondIso l k p q)
    (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q)

/-- 元の全 Hom 上で、既存の over 自然性自身の指定三角等式を回収する。 -/
lemma cocartesianOriginalOverNaturalityTriangleCommutes :
    CocartesianOriginalOverNaturalityTriangleCommutes l k p q := by
  have ha := (FunctorIso.sourceMap_postcomp
    (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q)
    (cocartesianBaseChangeHomCompositionNormalization l k p q)).symm.trans
    (cocartesianGlobalDirectNaturalityImage_source l k p q)
  have hb := (congrArg
    (fun m ↦ m ≫ cocartesianBaseChangeHomCompositionNormalization l k p q)
    (cocartesianOriginalOverNaturality_middle l k p q).symm).trans
    ((FunctorIso.targetMap_postcomp (cocartesianOriginalOverNaturalityIso l k p q)
      (cocartesianBaseChangeHomCompositionNormalization l k p q)).symm.trans
      (cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).2)
  have ht := (congrArg
    (fun m ↦ m ≫ cocartesianBaseChangeHomCompositionNormalization l k p q)
    (cocartesianOriginalOverNaturality_target l k p q).symm).trans
    (cocartesianOriginalOverNaturalitySecondIso_postcomp_target l k p q)
  exact (cocartesianLocalHomOverNormalization_isFullyFaithful l k p q).reflectFunctorIsoTriangle_of_heq
      (cocartesianOriginalOverNaturalityNormalizedIso l k p q)
      (cocartesianOriginalOverNaturalityNormalizedSecondIso l k p q)
      (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q)
      (cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q)
      ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
        (cocartesianBaseChangeHomRestrictionZero l k p q))
      (cocartesianBaseChangeGlobalTransportDirectIso l k p q) ha hb ht
      (cocartesianOriginalOverNaturalityNormalizedIso_postcomp_heq l k p q)
      (cocartesianOriginalOverNaturalityNormalizedSecondIso_postcomp_heq l k p q)
      (cocartesianGlobalTransportDirectIso_originalNaturality_heq l k p q).symm
      (cocartesianGlobalNativeRestrictionTriangleCommutes l k p q)

end SerrePositivity.InfinityCategories
