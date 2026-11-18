module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementUniversalAugmentation

/-!
概要：元の実 augmentation は普遍 cochain の全正次成分を零に送る。
方針：同じ恒等辺の定値単体の線形表示を使い、非単射引き戻しの成分を消す。
規約：任意の二点以上の部分集合と元の実 augmentation を保持する。
使われ方：大域 prism の augmentation 合成が恒等円柱となる成分式。
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

lemma normalizedTensorElementUniversalLinear_augmentation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (Fin.last n))))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X)))) := by
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (A := A) (D := Complex A) (x := X) (y := X))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalSimplex_augmentation A X Y c)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear _ _).symm.trans
    (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback _ _))

lemma normalizedTensorElementUniversalLinear_augmentation_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : 2 ≤ J.card) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (Fin.last n)))).f k
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component J k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) hk) = 0 := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A X X n =>
      s.val.component J k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) hk)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear_augmentation A X Y c)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj (A := A) (D := Complex A)
    (x := X) (y := X) _ _ J k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) hk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.not_injOn_constant hJ))

end SerrePositivity.ComplexLimits
