module

public import SerrePositivity.EInfinity.ComplexLimits.ProbeDerivedComparison

/-!
# 元の probe 比較の同じ頂点同型

概要：全関手同型の頂点成分を、元の probe 値を厳密な端点として回収する。
方針：nerve の零単体の計算で前合成の端点等式を明示する。
規約：元の比較の成分を選び直さない。
使われ方：標準導来単位と同じ始域比較を実 Hom の前合成に使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

def complexProbeDerivedSourceVertexIso (X : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((framedLimitProbeFunctor A).obj X)))
      ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) := by
  have hx : (nerveMap (framedLimitProbeFunctor A)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((framedLimitProbeFunctor A).obj X) := by
    change (nerveMap (framedLimitProbeFunctor A)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ X) = _
    rw [nerveMap_app_mk₀]
    rfl
  exact (eqToIso (congrArg HomotopyCategory.mk
    (congrArg ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)) hx))).symm ≪≫
      (complexProbeDerivedSourceIso A).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)

end SerrePositivity.EInfinity.ComplexLimits
