module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuSourceSquare
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEdgeDiagram

/-!
概要：元始域外周の実 S 四辺を同じ Cat^perf の四完全射へ照合する。
方針：元外面の四辺回収と同じ固定 ν の全区間表示を使う。
規約：元零角・実合成包含・resolved 商辺を保持する。
使われ方：元 LT 外周との指定四側面比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Src" => dgKInputStableValue R (dgOdotMilnorSourceCellInput R d)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R (dgFixedNullInput R (dgOdotMilnorSourceCellInput R d))
local notation "hC" => dgKInputStableValue_isIdempotentComplete R _

/-- 概要：元実外周の零左辺の同じ固定 ν 完全射。
方針：元全対象商包含を同じ ν で写す。規約：元零角を保持。
使われ方：元外周の指定零左側面。 -/
def dgOdotMilnorOuterNullLeftMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Src) (Z) :=
  dgKInputNuMap R (dgFixedNullLeft R (A := dgOdotMilnorSourceCellInput R d))

/-- 概要：元実外周の零上辺の同じ固定 ν 完全射。
方針：元二つの実零化延長の同じ合成を写す。規約：元合成を保持。
使われ方：元外周の指定零上側面。 -/
def dgOdotMilnorOuterNullTopMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Z) (Q) :=
  dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorSourceKernelNullContracted R d) ≫
    dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))

/-- 概要：実外周の Cat^perf 下辺は元の同じ合成包含。
方針：元 S 四辺と固定 ν の全区間回収を使う。規約：元包含を保持。
使われ方：外周の包含比較の端点照合。 -/
lemma dgOdotMilnorSourceNullOuterSquare_perfect_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorNuSourceInclusion R d) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorSourceNullOuterSquare_edges R d).1]
  exact dgKInputPerfectNu_edge_diagram R _

/-- 概要：実外周の Cat^perf 右辺は元の同じ resolved 射影。
方針：元 S 四辺と固定 ν の全区間回収を使う。規約：元射影を保持。
使われ方：外周の商比較の端点照合。 -/
lemma dgOdotMilnorSourceNullOuterSquare_perfect_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorCellProjectionExactMap R d) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorSourceNullOuterSquare_edges R d).2.1]
  exact dgKInputPerfectNu_edge_diagram R _

/-- 概要：実外周の Cat^perf 左辺は元の同じ全対象商包含。
方針：元 S 四辺と固定 ν の全区間回収を使う。規約：元零角を保持。
使われ方：外周の零左側面の端点照合。 -/
lemma dgOdotMilnorSourceNullOuterSquare_perfect_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorOuterNullLeftMap R d) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorSourceNullOuterSquare_edges R d).2.2.1]
  exact dgKInputPerfectNu_edge_diagram R _

/-- 概要：実外周の Cat^perf 上辺は元の同じ二零化延長の合成。
方針：元 S 四辺と固定 ν の全区間回収を使う。規約：元合成を保持。
使われ方：外周の零上側面の端点照合。 -/
lemma dgOdotMilnorSourceNullOuterSquare_perfect_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorOuterNullTopMap R d) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorSourceNullOuterSquare_edges R d).2.2.2]
  exact dgKInputPerfectNu_edge_diagram R _
end SerrePositivity.KST.SConstruction
