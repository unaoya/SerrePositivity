module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConePairEquation

/-!
概要：各元の単体要素への普遍 cone 辺を、HA 方程式を持つ実一単体として構成する。
方針：元の零単体列の生データに、全二点成分の閉性を適用する。
規約：実高次 cone は別工程。使われ方：大域 prism の指定された零次成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeEdgeSimplex (i : normalizedTensorElementIndex A X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 1 where
  toSimplexData := normalizedTensorConeData A X Y (ComposableArrows.mk₀ i)
  equation I a b k hI ha hb hk := by
    have hi : I.card ≤ 2 := by simpa using I.card_le_univ
    exact normalizedTensorConeData_equation_pair A X Y (ComposableArrows.mk₀ i) I
      (by omega) a b k hI ha hb hk

end SerrePositivity.EInfinity.ComplexLimits
