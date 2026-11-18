module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeUnderSimplex

/-!
概要：元の反対要素圏の全単体の実 cone を、同じ X 下の大域 coslice 写像へ束ねる。
方針：点と標準単体の join の自然性と、元の実 cone 単体の全自然性を使う。
規約：添字圏の始対象性は仮定しない。使われ方：同じ実 cone/prism と元の屋根の比較。
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

def normalizedTensorConeUnderMap : nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X) where
  app _ := ↾fun c => _root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderSimplex A X Y c
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y
            ((nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).map α c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.stdSimplex.map α.unop) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso m.unop.len).hom ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
            (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left]
    have hn := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex_naturality A X Y c α.unop
    exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n.unop.len + 1) =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm s) hn

lemma normalizedTensorConeUnderMap_app {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderMap A X Y).app (Opposite.op ⦋n⦌) c =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderSimplex A X Y c := rfl

end SerrePositivity.ComplexLimits
