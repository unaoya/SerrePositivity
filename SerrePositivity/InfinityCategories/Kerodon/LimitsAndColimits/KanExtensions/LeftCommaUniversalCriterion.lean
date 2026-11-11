module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaUniversalFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaUniversalIdentity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaRelativeCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftHomotopyInvariant
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftJoinCriterion

/-!
概要：普遍図式への前合成が標準の相対左 Kan 条件を保ち反映することを示す。
方針：候補の指定変換の類は恒等であり、comma fiber の局所判定を使う。
規約：同じ底での選択を全ての標的・関手に使う。
使われ方：元の Kan 関手の全部分圏と相対 join 図式の全部分圏の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：普遍自己変換を任意の関手で写した変換の類も恒等射。
方針：後合成の関手はホモトピー圏の恒等射を保つ。
規約：raw な変換が定値であるとは仮定しない。
使われ方：普遍図式から得た候補の変換を恒等の指定変換と比較する。 -/
lemma kanLeftCommaUniversalIdentityHomotopy_postcomp_hom {K C D : SSet.{u}}
    [Quasicategory C] (δ : K ⟶ C) (F : C ⟶ D) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalIdentityHomotopy δ) F)) =
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalIdentityHomotopy_hom,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
  exact CategoryTheory.Functor.map_id _ _

/-- 概要：標準の相対左 Kan 条件は普遍図式への前合成後の全 fiber の U 余極限性と同値。
方針：候補の関手は厳密に F であり、候補の指定変換の類は恒等射である。
規約：U は inner fibration。δ の単射性はこの局所比較には不要。
使われ方：元の相対左 Kan 関手の族を相対 join の普遍図式の族へ写す。 -/
lemma kanIsRelativeLeftKanExtendedFrom_iff_universal_fibers {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F ↔
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ (δ ≫ F) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily_diagram δ F
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidateTransformation δ (δ ≫ F) H hH
  let α := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalIdentityHomotopy δ) F
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtension_iff_of_diagram_eq_of_h_eq U δ rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily_candidate δ F) β α (by rfl)
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtension_iff_of_homMk_eq U δ (δ ≫ F) F α
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F)) (kanLeftCommaUniversalIdentityHomotopy_postcomp_hom δ F)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension U δ F).trans
    (hh.symm.trans (he.symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate_isRelativeLeftKanExtension_iff U δ (δ ≫ F) H hH)))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
