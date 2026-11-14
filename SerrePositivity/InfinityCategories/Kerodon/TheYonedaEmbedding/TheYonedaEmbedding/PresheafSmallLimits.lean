module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafPointwiseLimits
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.SpaceLimitShapes

/-!
概要：小さい形状での空間の極限の存在を、元の前層図式の極限と全評価へ移す。
方針：各評価図式に同じ形状の空間値極限を適用する。
規約：形状の極限の存在は明示し、前層の各点存在や同値性を instance 仮定にしない。
使われ方：F1-4 の各点構成と F2・N の空間値極限の提供界面の接続。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {B C : SSet.{u}}
  (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
  (hB : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.HasSpaceLimitsOfShape B)
include hB

/-- 小さい形状の空間値極限から、同じ前層図式の全極限錐を構成する。 -/
lemma presheafInfinity_exists_limitCone_of_spaceLimitsOfShape :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ ∀ x : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_exists_limitCone_of_evaluation p (fun x ↦ hB _)

/-- 同じ小さい形状の全空間値図式に極限があれば、前層図式にも極限が存在する。 -/
lemma presheafInfinity_hasLimit_of_spaceLimitsOfShape : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasLimit_of_evaluation p (fun x ↦ hB _)

/-- 同じ空間値形状の存在から、元の全評価による極限の保存・検出を得る。 -/
lemma presheafInfinity_isLimit_iff_evaluation_of_spaceLimitsOfShape (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ x : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_isLimit_iff_evaluation p (fun x ↦ hB _) c

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
