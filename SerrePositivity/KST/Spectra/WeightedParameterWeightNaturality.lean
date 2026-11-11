module

public import SerrePositivity.KST.Spectra.WeightedParameterNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：共有の weighted end のパラメータ作用と重みの制限の両立。
方針：各射影で源制限の評価式を使い、結合子の二変数の自然性を比較する。
規約：重みの射の単射性や弱同値性は不要。使われ方：反転比較の共通解像への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.WeightedParameterNaturality
variable {I : Type u} [SmallCategory I]

/-- 重みの制限は各射影で元の重みの射の前合成になる。 -/
@[reassoc]
lemma pre_evaluation {W V : I ⥤ SSet.{u}} (j : W ⟶ V) (H : I ⥤ SSet.{u}) (i : I) :
    W.obj i ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) =
      j.app i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i) := by
  rw [← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π, uncurry_pre_app]

/-- 重みの制限は係数の全パラメータ作用と可換。 -/
lemma weight_natural {W V : I ⥤ SSet.{u}} (j : W ⟶ V) {H E : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : H ⋙ tensorRight B ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H ▷ B ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W η =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap V η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j E := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  apply uncurry_injective
  conv_lhs =>
    rw [Category.assoc, uncurry_natural_left, uncurry_natural_left,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap_evaluation, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, pre_evaluation, comp_whiskerRight_assoc]
  conv_rhs =>
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π, ← Category.assoc, uncurry_pre_app,
      uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap_evaluation,
      associator_inv_naturality_left_assoc]

end SerrePositivity.KST.Spectra.WeightedParameterNaturality
