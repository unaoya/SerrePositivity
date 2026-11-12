module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSliceComparisonEquivalence

/-!
概要：元の指定頂点の slice を、元の関手の像の点の局所 Kan 添字へ比較する。
方針：同じ slice 比較と引き戻しの因子交換を合成し、元の恒等錐を追跡する。
規約：元の関手に inner 性を仮定しない。恒等頂点を厳密に保つ。
使われ方：指定 Kan 単位の成分の可逆性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C D : SSet.{u}} (f : C ⟶ D) (y : C _⦋0⦌)
local notation "t" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))

instance pointLeftKanProjection_rightFibration [Quasicategory D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection f (f.app (Opposite.op ⦋0⦌) y)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_fst _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := t))⟩

instance pointLeftKanShape_quasicategory [Quasicategory C] [Quasicategory D] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape f (f.app (Opposite.op ⦋0⦌) y)) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection f (f.app (Opposite.op ⦋0⦌) y))

/-- 元の slice から、同じ像の点の元の局所 Kan 添字への比較。 -/
def pointSliceKanComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape f (f.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison f y ≫ (pullbackSymmetry t f).hom

lemma pointSliceKanComparison_projection :
    pointSliceKanComparison f y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection f (f.app (Opposite.op ⦋0⦌) y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y) := by
  rw [pointSliceKanComparison, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison_projection f y

lemma pointSliceKanComparison_slice :
    pointSliceKanComparison f y ≫ pullback.snd f t = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp f y := by
  rw [pointSliceKanComparison, Category.assoc, pullbackSymmetry_hom_comp_snd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison, pullback.lift_fst]

/-- 同じ比較は、元の恒等錐を像の点の元の局所恒等頂点へ写す。 -/
lemma pointSliceKanComparison_identity :
    (pointSliceKanComparison f y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanIdentityVertex f y := by
  apply SSet.yonedaEquiv.symm.injective
  have hy : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone y) ≫ pointSliceKanComparison f y =
      SSet.yonedaEquiv.symm ((pointSliceKanComparison f y).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone y)) := SSet.yonedaEquiv_symm_comp _ _
  rw [← hy, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanIdentityVertex, Equiv.symm_apply_apply]
  apply pullback.hom_ext
  · rw [Category.assoc, pointSliceKanComparison_projection, pullback.lift_fst]
    simpa only [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone_projection]
  · rw [Category.assoc, pointSliceKanComparison_slice, pullback.lift_snd]
    simpa only [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp_identity]

/-- 充満忠実な元の関手では、同じ局所 Kan 比較自体が同値。 -/
lemma pointSliceKanComparison_isQCatEquivalence [Quasicategory C] [Quasicategory D]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pointSliceKanComparison f y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison_isQCatEquivalence f hf y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pullbackSymmetry t f)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
