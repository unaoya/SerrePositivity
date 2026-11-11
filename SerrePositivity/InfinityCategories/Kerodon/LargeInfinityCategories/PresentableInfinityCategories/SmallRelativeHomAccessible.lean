module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallRelativeOverHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteRelativeHomAccessible

/-!
概要：μ-small な底上始域の全相対 Hom は、一般の小さい μ-filtered ∞ 余極限を保つ。
方針：元の全余錐を共同 strict 化し、底上の通常の保存性を全自然比較と cofinal 制限で戻す。
規約：非可算正則 μ を要求し、元の指定余錐と全相対 Hom 関手を保持する。
使われ方：引き戻しの小さい compact 図式の同期と全パラメータの因子化。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：μ-small な始域の元の相対 Hom は、strict μ-filtered 全余錐を native に保存する。
方針：底上の通常の余極限保存を、同じ豊穣評価の全 join 射へ移す。
規約：底の quasicategory 性を要求しない。
使われ方：元の coherent 余錐との比較の入力。 -/
lemma smallRelativeHom_preserves_strictCocone
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {B : SSet.{u}} (A : Over B) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A.left)
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J μ]
    {F : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} (c : Cocone F)
    (hc : IsColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationObjectForget B).mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation A) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c)) := by
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J μ
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallRelativeOverHom_preservesCardinalFilteredColimits hμ A hA J
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeHom_strictCocone_postcomp_val A c)).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictNativeCocone_isColimit_of_filtered_forget
  change IsColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeOverHomFunctor A).mapCocone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationObjectForget B).mapCocone c))
  exact isColimitOfPreserves (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeOverHomFunctor A) hc

/-- 概要：通常の μ-filtered 添字上の元の coherent 全余錐を相対 Hom が保存する。
方針：共同 strict 化で同じ元の全図式と余錐の像を比較する。
規約：底は任意の小さい quasicategory、始域には μ-small 性のみを課す。
使われ方：一般 coherent 添字への cofinal 還元。 -/
lemma smallRelativeHom_preserves_nerveCocone
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {B : SSet.{u}} [Quasicategory B] (A : Over B) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A.left)
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J μ]
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation A) c) := by
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J μ
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationDiagramStrictification G
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.filteredLeftFibrationCocone F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.mapJoinCocone_isColimit_of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationDiagramStrictificationIso G) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone d) c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.filteredLeftFibrationCocone_isColimit F) hc
    (smallRelativeHom_preserves_strictCocone hμ A hA d (colimit.isColimit _))

/-- 概要：μ-small な底上始域からの元の全相対 Hom 関手は μ-accessible。
方針：指定全余錐を cofinal μ-filtered poset に制限し、元の同じ全相対 Hom 像へ戻す。
規約：余極限の頂点の比較だけでなく全余錐の保存を結論する。
使われ方：μ-small な図式の解の同時因子化。 -/
lemma smallRelativeHom_isKappaAccessibleFunctor
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {B : SSet.{u}} [Quasicategory B] (A : Over B) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation A) := by
  intro K hK hFiltered G c hc
  obtain ⟨J, o, f, hJ, _, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset (κ := μ) K
  let := o
  have := hJ
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift f hf
  have hc' := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal r hr c).mp hc
  have h := smallRelativeHom_preserves_nerveCocone hμ A hA (r ≫ G) (c.restrict r) hc'
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal r hr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation A) c)).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _)).mp h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
