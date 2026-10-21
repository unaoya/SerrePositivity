module

public import SerrePositivity.InfinityCategories.F1.CocartesianLocalHomOverNaturalityGlobalEndpoints
public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalNativeRestrictionTriangle

/-!
概要：元の底上の指定自然性の像は、大域自然性と同じ三角等式を満たす。
方針：両端表示だけを揃えた像を既存の指定 native 自然性へ同定する。
規約：元の全 Hom 上の既存の over 自然性を保持する。
使われ方：充満忠実な後合成で反映する三角等式。
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

/-- 両端の表示だけを揃えた、元の全 Hom 上の over 自然性の同じ像。 -/
def cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso :
    FunctorIso (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap
      (cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap :=
  F2.isoNormalizeEndpoints (cocartesianLocalHomOverNaturalityOriginalHomImageIso l k p q)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).1)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).2)

/-- 同じ over 自然性の正規化した像は、元の指定二因子の合成そのもの。 -/
lemma cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso_eq :
    cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso l k p q =
      cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q := by
  exact F2.isoNormalizeEndpoints_eq_of_heq
    (cocartesianLocalHomOverNaturalityOriginalHomImageIso l k p q)
    (cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).1)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m))
      (cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).2)
    ((cocartesianLocalHomComparison_overNaturalityIso_originalHom_postcomp_heq l k p q).trans
      (cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_heq l k p q))

/-- 元の全 Hom 上の、同じ over 自然性の像と大域自然性との三角等式。 -/
def CocartesianOriginalOverNaturalityImageTriangleCommutes : Prop :=
  IsoTriangleCommutes (cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso l k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q))
    (cocartesianBaseChangeGlobalTransportDirectIso l k p q)

/-- 同じ指定 over 自然性の像は、元の大域自然性の三角等式を満たす。 -/
lemma cocartesianOriginalOverNaturalityImageTriangleCommutes :
    CocartesianOriginalOverNaturalityImageTriangleCommutes l k p q := by
  exact IsoTriangleCommutes.replace_first
    (cocartesianGlobalNativeRestrictionTriangleCommutes l k p q)
    (cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso l k p q)
    (heq_of_eq (cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso_eq l k p q))

end SerrePositivity.InfinityCategories
