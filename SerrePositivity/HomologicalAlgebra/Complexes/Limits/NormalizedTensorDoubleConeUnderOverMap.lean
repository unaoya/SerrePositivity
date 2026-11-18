module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeUnderOverSimplex

/-!
概要：同じ終端 X 上の slice 内で、元の全二重 cone 単体を大域 coslice 写像へ束ねる。
方針：始点付き全作用素の自然性と、点と標準単体の join の自然性を使う。
規約：同じ元の要素圏・恒等錐を保持する。使われ方：大域二重 join。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorDoubleConeUnderOverMap : nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.ComplexLimits.normalizedTensorIdentityOverPoint A X) where
  app _ := ↾fun c => _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeUnderOverSimplex A X Y c
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X))).symm
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverSimplex A X Y
            ((nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).map α c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.stdSimplex.map α.unop) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso m.unop.len).hom ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X))).symm
            (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverSimplex A X Y c))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left]
    have hn := _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverSimplex_naturality A X Y c α.unop
    exact congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X)) _⦋n.unop.len + 1⦌ =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X))).symm s) hn

lemma normalizedTensorDoubleConeUnderOverMap_app {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeUnderOverMap A X Y).app (Opposite.op ⦋n⦌) c =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeUnderOverSimplex A X Y c := rfl

end SerrePositivity.ComplexLimits
