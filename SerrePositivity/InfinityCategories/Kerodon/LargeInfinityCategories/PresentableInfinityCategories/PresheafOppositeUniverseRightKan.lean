module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafOppositeRightKanCriterion
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UniverseRightKanCanonical
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-!
概要：反対密度錐の像から一段大きい宇宙の全右 Kan 条件を導く。
方針：同じ小さい elements 比較を持ち上げ、標準右 Kan 錐の宇宙比較を使う。
規約：元の前層圏や表現対象を大きい前層圏へ置き換えない。
使われ方：小さい空間値関手と元の大きい表現可能 Hom の全自然比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 2}} [Quasicategory E]
  (q : (SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A).op ⟶ E)

/-- 概要：持ち上げた反対密度錐の像の極限性から標準右 Kan 錐の像の極限性を得る。
方針：持ち上げた元の elements 比較で制限し、全錐の射の一致を使う。
規約：指定した元の前層と元の全密度錐を保持する。
使われ方：元の反対 Yoneda に沿う宇宙を分けた右 Kan 判定。 -/
lemma presheaf_oppositeDensity_image_canonicalLimits
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone P))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)) (𝟙 _)
        (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex P))))) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A))
    (𝟙 _) (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex P))
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsRightKanComparison P
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u + 1, u + 2}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsRightKanComparison_isQCatEquivalence P)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e) he _).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ ?_).mpr h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 2, u + 1}).map e) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2} c).val ≫ q) = _
  rw [← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2} c)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e)).val ≫ q = _
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafRightKanCanonicalCone_restrict_val (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A).op) P
  have hv₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c e).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone P)).val :=
    hv.trans (Category.comp_id _)
  exact (congrArg (fun g ↦ g ≫ q)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_restrictJoinCone_val.{u + 1, u + 2} c e).symm).trans
      (congrArg (fun g ↦ ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso _ 0).inv ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map g) ≫ q) hv₀)

/-- 概要：全反対密度錐を保つ元の大きい空間値関手は右 Kan 延長。
方針：元の全標準右 Kan 錐の像の極限性を宇宙比較の判定へ渡す。
規約：元の反対 Yoneda と同じ恒等指定変換を使う。
使われ方：表現可能前層と小さい空間値関手の全自然同型。 -/
lemma presheaf_oppositeDensity_image_isRightKanExtension
    (h : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone P))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)) ≫ q) q
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl
        ((SSet.uliftFunctor.{u + 2, u + 1}).map
          (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)) ≫ q)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanExtension_refl_post_ulift_of_canonicalLimits _ (𝟙 _) q
  intro v
  obtain ⟨P, hP⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv A).surjective (SSet.opObjEquiv v)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex P = SSet.opObjEquiv v at hP
  have hv : v = SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex P) := by rw [hP]; rfl
  rw [hv]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_oppositeDensity_image_canonicalLimits q P (h P)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
