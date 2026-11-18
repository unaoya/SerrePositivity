module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeWithoutFirst
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeObjects

/-!
概要：元の普遍 cochain と frame 図式を接合し、実 cone の全単体データを構成する。
方針：始点を含む成分には選択普遍 cochain、他の成分には元の通常単体を使う。
規約：HA 方程式は別工程で証明する。使われ方：大域比較を与える実 cone/prism。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeData {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) (n + 1) where
  obj := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c
  hom I a b k hI ha hb hk := by
    have hab : a < b := by
      rw [ha, hb]
      exact I.min'_lt_max'_of_card (by omega)
    have hb0 : b ≠ 0 := ne_of_gt ((Fin.zero_le a).trans_lt hab)
    by_cases ha0 : a = 0
    · have h0 : (0 : Fin (n + 2)) ∈ I := by
        rw [← ha0, ha]
        exact I.min'_mem _
      have hJ := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
      have hc := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0
      have hk' : k = 1 - ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card : ℤ) := by omega
      have hb' : b = ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' hJ).succ :=
        hb.trans (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.max_withoutFirst I hI h0).symm
      exact cast (by rw [ha0, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_zero, hb', _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_succ])
        (k.negOnePow •
          _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k hJ hk')
    · exact cast (by
        rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex_obj, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex_obj,
          _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_ne_zero A X Y c a ha0,
          _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_ne_zero A X Y c b hb0])
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex A X Y c).toSimplexData.hom I a b k hI ha hb hk)

end SerrePositivity.ComplexLimits
