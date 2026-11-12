module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnderSectionScaffoldEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.OverComparisonResolution

/-!
概要：元の共同 left fibration と strict weighted nerve を、元の積上の同値の span で結ぶ。
方針：二つの元の scaffold を同じ inner anodyne 置換へ延長し、その制限と射影を保持する。
規約：全空間の同値の存在だけに弱めず、元の大域射を回収する同じ比較データを保存する。
使われ方：元の coherent 前層図式と strict 分類図式の大域分類比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 元の積、元の両 scaffold とその制限を保持する一つの復元 span。 -/
structure UnderSectionReconstruction where
  space : SSet.{u}
  inclusion : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p) ⟶ space
  projection : space ⟶ B ⊗ nerve I
  left : space ⟶ E
  right : space ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p)
  inclusion_innerAnodyne : innerAnodyneExtensions inclusion
  projection_innerFibration : InnerFibration projection
  inclusion_projection : inclusion ≫ projection =
    lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffoldBase p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p))
  left_restriction : inclusion ≫ left = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffold p
  right_restriction : inclusion ≫ right = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p)
  left_projection : left ≫ p = projection
  right_projection : right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionWeightedProjection p = projection
  left_equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence left
  right_equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence right

/-- 両方の元の大域比較を延長した、同じ積上の復元 span が存在する。 -/
lemma nonempty_underSectionReconstruction [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Nonempty (UnderSectionReconstruction p) := by
  obtain ⟨Z, j, t, a, b, hj, ht, hjt, hja, hjb, hat, hbt, ea, eb⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_innerFibration_comparison_span
      (lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffoldBase p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p)))
      p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionWeightedProjection p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffold p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffold_over_product p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTautScaffold_over_product p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffold_isPrecompositionEquivalence p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTautScaffold_isPrecompositionEquivalence p)
  exact ⟨{
    space := Z
    inclusion := j
    projection := t
    left := a
    right := b
    inclusion_innerAnodyne := hj
    projection_innerFibration := ht
    inclusion_projection := hjt
    left_restriction := hja
    right_restriction := hjb
    left_projection := hat
    right_projection := hbt
    left_equivalence := ea
    right_equivalence := eb }⟩

/-- 元の全空間と strict weighted nerve を結ぶ、両制限を保持した一つの復元データ。 -/
def underSectionReconstruction [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    UnderSectionReconstruction p := Classical.choice (nonempty_underSectionReconstruction p)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
