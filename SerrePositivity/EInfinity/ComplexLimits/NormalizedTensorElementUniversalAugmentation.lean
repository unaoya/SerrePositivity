module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversalEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversalLinear

/-!
概要：同じ実 augmentation は全普遍単体を元の恒等辺の定値単体へ送る。
方針：元の全族の恒等式を同じ恒等単体で評価する。
規約：元の augmentation 頂点を置き換えず、同じ恒等辺を保持する。
使われ方：大域 prism と同じ全 augmentation の合成端点の照合。
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
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementUniversalSimplex_augmentation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X
        ((normalizedTensorElementAugmentation A X Y).app (c.obj (Fin.last n))))).app
          (Opposite.op ⦋n⦌) (normalizedTensorElementUniversalSimplex A X Y c) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X X).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map (𝟙 X))) := by
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X X =>
      f.app (Opposite.op ⦋n⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))))
    (normalizedTensorElementUniversalFamily_augmentation A X Y c)
  exact h

end SerrePositivity.EInfinity.ComplexLimits
