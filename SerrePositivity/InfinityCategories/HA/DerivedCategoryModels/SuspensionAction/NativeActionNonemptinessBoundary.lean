module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.NativeActionRequirement

/-!
概要：零／disk の反例が採用作用全体の空性をまだ示さない、正確な型の境界。
方針：固定 data を回収する追加条件を明記し、自由な data には自己比較があることを示す。
規約：最終商関手圏での固定二辺の比較の非存在も、全作用の存在も主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
variable (R : Type u) [CommRing R]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- 同じ端点を持つ二つの点関手に、採用境界が許す data の共通の型。 -/
abbrev nativeDiskAdmissibleSuspensionData :=
  DGKappaSuspensionMapData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskSourceInput.{u, v} R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskTargetInput.{u, v} R)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskSourceInput.{u, v} R) κ hκ)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskTargetInput.{u, v} R) κ hκ)

/-- 許された data が与える、最終商関手圏の native 頂点。 -/
def nativeDiskAdmissibleSuspensionVertex
    (d : nativeDiskAdmissibleSuspensionData.{u, v} R κ hκ) :=
  dgFunctorNativeMappingVertex R _ _
    (dgKappaSuspensionInputMap R _ _ _ _ d).down

/-- data が同じなら、二つの入力辺の出力として選べる頂点には自己同型がある。 -/
def nativeDiskCommonDataComparison
    (d : nativeDiskAdmissibleSuspensionData.{u, v} R κ hκ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (nativeDiskAdmissibleSuspensionVertex R κ hκ d)
      (nativeDiskAdmissibleSuspensionVertex R κ hκ d) := Iso.refl _

/-- 全ての許された data の組について比較が存在しない、という強い主張は偽。 -/
theorem not_nativeDisk_all_admissible_data_separated :
    ¬ (∀ d e : nativeDiskAdmissibleSuspensionData.{u, v} R κ hκ,
      ¬ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (nativeDiskAdmissibleSuspensionVertex R κ hκ d)
        (nativeDiskAdmissibleSuspensionVertex R κ hκ e))) := by
  intro h
  let d := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskZeroInputMap.{u, v} R)
  exact h d d ⟨nativeDiskCommonDataComparison R κ hκ d⟩

/-- 固定二辺の data が一致することは、採用構造の外で課す追加条件である。 -/
def nativeDiskActionUsesFixedData
    (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ)) : Prop :=
  a.data (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskZeroInputMap.{u, v} R) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskZeroInputMap.{u, v} R) ∧
  a.data (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskNonzeroInputMap.{u, v} R) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskNonzeroInputMap.{u, v} R)

/-- 最終商関手圏で固定比較を否定できた場合に限り得られる、固定 data 付き作用の否定。
端点固定 edgeIso は nativeDiskSuspensionComparisonOfAction 内で既に考慮されている。 -/
theorem no_nativeDisk_fixedData_action_of_no_comparison
    (h : ¬ Nonempty (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskSuspensionComparisonType.{u, v} R κ hκ)) :
    ¬ ∃ a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ),
      nativeDiskActionUsesFixedData R κ hκ a := by
  rintro ⟨a, hf, hg⟩
  exact h ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.nativeDiskSuspensionComparisonOfAction R κ hκ a hf hg⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
