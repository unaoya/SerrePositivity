module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.WeightedEndDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallEndIndex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallInternalHomContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallStrictLimitExchange

/-!
概要：小さい重み付き切断関手は、同じ μ-filtered な通常の余極限を保つ。
方針：各内部 Hom の保存と小さい end の極限の保存を、元の関手の自然同型で合成する。
規約：元の weightedSectionsFunctor とその全誘導射を保持。native な ∞ 極限の交換とは区別する。
使われ方：Bousfield–Kan 模型から全 coherent な交換へ進むための連続性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


variable {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
  {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u})
  (hW : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (W.obj i)) (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
include hμ hW

/-- 元の end 図式の各成分は、μ-small な重みからの内部 Hom の保存によって連続。 -/
lemma weightedEndDiagramFunctor_preservesCardinalFilteredColimits :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.weightedEndDiagramFunctor W) := by
  have (i : I) : PreservesColimitsOfShape J (ihom (W.obj i)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallInternalHom_preservesCardinalFilteredColimits hμ _ (hW i) J
  apply preservesColimitsOfShape_of_evaluation
  intro x
  cases x with
  | left i =>
    exact inferInstanceAs (PreservesColimitsOfShape J
      (((evaluation I SSet.{u}).obj i) ⋙ ihom (W.obj i)))
  | right f =>
    exact inferInstanceAs (PreservesColimitsOfShape J
      (((evaluation I SSet.{u}).obj f.right) ⋙ ihom (W.obj f.left)))

/-- 重みと全射の総数が小さければ、元の weighted sections 関手は μ-filtered 余極限を保つ。 -/
lemma weightedSectionsFunctor_preservesCardinalFilteredColimits (hI : HasCardinalLT (Arrow I) μ) :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor W) := by
  have := weightedEndDiagramFunctor_preservesCardinalFilteredColimits hμ W hW J
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallSSetLimit_preservesCardinalFilteredColimits
    (WalkingMulticospan (multicospanShapeEnd I)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasCardinalLT_endIndex_arrow hμ.le I hI) J
  have : PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.weightedEndDiagramFunctor W ⋙ lim) := inferInstance
  exact preservesColimitsOfShape_of_natIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.weightedSectionsLimitIso W).symm

/-- 同じ重み付き切断について、元の μ-filtered strict 余極限との標準比較同型。 -/
def weightedSectionsCardinalFilteredIso (hI : HasCardinalLT (Arrow I) μ)
    (F : J ⥤ I ⥤ SSet.{u}) :
    colimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor W) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (colimit F) := by
  have := weightedSectionsFunctor_preservesCardinalFilteredColimits hμ W hW J hI
  exact (preservesColimitIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor W) F).symm

/-- 同じ比較同型は、元の各余極限脚を元の weightedSectionsMap へ厳密に戻す。 -/
lemma weightedSectionsCardinalFilteredIso_ι (hI : HasCardinalLT (Arrow I) μ)
    (F : J ⥤ I ⥤ SSet.{u}) (j : J) :
    colimit.ι (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor W) j ≫
      (weightedSectionsCardinalFilteredIso hμ W hW J hI F).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W (colimit.ι F j) := by
  have := weightedSectionsFunctor_preservesCardinalFilteredColimits hμ W hW J hI
  exact ι_preservesColimitIso_inv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor W) F j

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
