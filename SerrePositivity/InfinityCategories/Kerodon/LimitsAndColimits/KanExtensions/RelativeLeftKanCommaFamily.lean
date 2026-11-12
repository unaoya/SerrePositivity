module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaUniversalCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRelativeUniversalRestriction

/-!
概要：元の相対左 Kan 関手の全部分圏から comma の相対普遍図式への族の写像。
方針：底で選んだ普遍図式への前合成を頂点条件で全部分複体へ制限する。
規約：関手ごとの表示を選び直さず、全次数の族を一つの単体写像で扱う。
使われ方：相対写像空間の制限定理を元の関手の全部分圏へ戻す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：関手頂点が表す F が δ から相対左 Kan 拡張されている条件。
方針：頂点を実際の関手へ戻し、標準局所 U 余極限条件を使う。
規約：大域的な写像空間の普遍性を定義には含めない。
使われ方：元の関手圏内の相対左 Kan 関手の全部分複体。 -/
def KanRelativeLeftKanVertex {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (x : ((ihom C).obj D) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm x)

/-- 概要：δ から相対左 Kan 拡張されている関手の全部分単体集合。
方針：標準局所条件を持つ頂点の張る全部分複体を取る。
規約：相対 join の図式ではなく、元の C 上の関手を対象とする。
使われ方：元の全部分圏からの制限の主経路の始域。 -/
def kanRelativeLeftKanDiagrams {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C) :
    ((ihom C).obj D).Subcomplex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeLeftKanVertex U δ)

/-- 概要：元の相対左 Kan 関手の族を comma の局所相対普遍図式の族へ写す。
方針：普遍図式への前合成が標準相対左 Kan 条件を保つことを使い全部分複体へ持ち上げる。
規約：U は inner fibration。δ 自体の単射性はこの構成には不要。
使われ方：元の関手圏と相対 join の関手圏の写像空間の比較。 -/
def kanRelativeLeftKanToCommaDiagrams {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) :
    (kanRelativeLeftKanDiagrams U δ : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeColimitDiagrams (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) U : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeJoinRelativeColimitVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) U)
    ((kanRelativeLeftKanDiagrams U δ).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily δ D) (by
      intro x
      let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm x.val
      have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = x.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).apply_symm_apply _
      have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F at hx
      have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_universal_fibers U δ F).1 hx
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeJoinRelativeColimitVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) U
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily δ D).app (Opposite.op ⦋0⦌) x.val)
      rw [← hF]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeJoinRelativeColimitVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) U
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F))
      intro c
      have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C)) D).symm
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F)) =
              _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).symm_apply_apply _
      rw [he]
      exact hc c)

/-- 概要：comma への族の比較は通常の関手圏への包含後に普遍前合成と一致する。
方針：全部分複体への持ち上げの包含の計算を使う。
規約：単体写像の厳密な等式。
使われ方：写像空間の比較における実際の前合成の作用。 -/
lemma kanRelativeLeftKanToCommaDiagrams_ι {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) :
    kanRelativeLeftKanToCommaDiagrams U δ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeColimitDiagrams (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) U).ι =
        (kanRelativeLeftKanDiagrams U δ).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily δ D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：comma へ写した相対左 Kan 関手の族を右端へ制限すると元の族を回収する。
方針：包含後の前合成の式と普遍図式の右端の恒等性を合わせる。
規約：関手とその高次の族を厳密に保つ。
使われ方：元の関手 F を固定して比較するための切断の式。 -/
lemma kanRelativeLeftKanToCommaDiagrams_inr {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) :
    kanRelativeLeftKanToCommaDiagrams U δ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeColimitDiagrams (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) U).ι ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C))).app D =
          (kanRelativeLeftKanDiagrams U δ).ι := by
  rw [← Category.assoc, kanRelativeLeftKanToCommaDiagrams_ι,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily_inr, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
