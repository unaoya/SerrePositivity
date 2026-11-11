module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalColimitFiberAssembly
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinCoconeTransport
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：comma の相対 join の図式の右端と、元の添字上の指定変換を取り出す。
方針：右包含で候補を定義し、標準 prism を恒等矢印の包含に制限する。
規約：候補と変換の抽出に充填性は不要。
使われ方：局所余極限から組み立てた図式を左 Kan 拡張の候補へ戻す。

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

/-- 概要：comma の相対 join の図式の右端は元の底上の図式。
方針：底 C の右包含を前合成する。
規約：δ は任意の関手。
使われ方：左 Kan 拡張の候補の図式。 -/
def kanLeftCommaCandidate {K C D : SSet.{u}} (δ : K ⟶ C)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D) : C ⟶ D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H

/-- 概要：左端で元の図式を保つ comma の図式は元の添字上に指定変換を与える。
方針：相対 join の標準変換を恒等矢印の包含に制限し、両射影を計算する。
規約：変換の向きは F₀ から δ に沿う候補の制限。
使われ方：点ごとの左 Kan 条件の入力。 -/
def kanLeftCommaCandidateTransformation {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) :
    SSet.Homotopy F₀ (δ ≫ kanLeftCommaCandidate δ H) := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinTransformation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)
  refine {
    h := T.h
    h₀ := ?_
    h₁ := ?_
    rel := T.rel }
  · rw [T.h₀, hH, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source, Category.id_comp]
    rfl
  · rw [T.h₁, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_projection]
    rfl

/-- 概要：局所余極限があれば各 fiber で普遍な図式と元の添字上の指定変換を同時に得る。
方針：coherent な図式の存在を使い、右端と標準変換を抽出する。
規約：ここでは指定変換が左 Kan 条件を満たすことはまだ結論しない。
使われ方：標準局所余錐との比較に使う候補データ。 -/
lemma exists_kanLeftComma_candidate {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)) :
    ∃ (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
      (_hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀),
      Nonempty (SSet.Homotopy F₀ (δ ≫ kanLeftCommaCandidate δ H)) ∧
        ∀ c : C _⦋0⦌,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c H) := by
  obtain ⟨H, hH, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftComma_diagram_with_colimit_fibers δ F₀ hcol
  exact ⟨H, hH, ⟨kanLeftCommaCandidateTransformation δ F₀ H hH⟩, hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
