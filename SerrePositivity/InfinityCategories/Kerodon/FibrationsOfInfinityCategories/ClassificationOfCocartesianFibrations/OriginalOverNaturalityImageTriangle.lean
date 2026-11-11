module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalHomOverNaturalityGlobalEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OriginalNativeRestrictionTriangle

/-!
概要：元の底上の指定自然性の像は、大域自然性と同じ三角等式を満たす。
方針：両端表示だけを揃えた像を既存の指定 native 自然性へ同定する。
規約：元の全 Hom 上の既存の over 自然性を保持する。
使われ方：充満忠実な後合成で反映する三角等式。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 両端の表示だけを揃えた、元の全 Hom 上の over 自然性の同じ像。 -/
def cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomOverNaturalityOriginalHomImageIso l k p q)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).1)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).2)

/-- 同じ over 自然性の正規化した像は、元の指定二因子の合成そのもの。 -/
lemma cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso_eq :
    cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso l k p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q := by
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints_eq_of_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomOverNaturalityOriginalHomImageIso l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).1)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).2)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison_overNaturalityIso_originalHom_postcomp_heq l k p q).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison_nativeRestrictionIso_originalHom_heq l k p q))

/-- 元の全 Hom 上の、同じ over 自然性の像と大域自然性との三角等式。 -/
def CocartesianOriginalOverNaturalityImageTriangleCommutes : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes (cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso l k p q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomRestrictionZero l k p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTransportDirectIso l k p q)

/-- 同じ指定 over 自然性の像は、元の大域自然性の三角等式を満たす。 -/
lemma cocartesianOriginalOverNaturalityImageTriangleCommutes :
    CocartesianOriginalOverNaturalityImageTriangleCommutes l k p q := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes.replace_first
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianGlobalNativeRestrictionTriangleCommutes l k p q)
    (cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso l k p q)
    (heq_of_eq (cocartesianLocalHomOverNaturalityOriginalHomNormalizedImageIso_eq l k p q))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
