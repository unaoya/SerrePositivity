module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementUniversal
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorAugmentationIdentity

/-!
概要：全単体列の普遍族を元の評価射と augmentation で送る厳密な式。
方針：同じ終端パラメータで元の普遍評価と恒等定数族を引き戻す。
規約：元の二つの自然変換の終端成分を保つ。
使われ方：大域 prism の二つの合成端点の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementUniversalFamily_evaluation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily A X Y c ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
        (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)))) =
    SSet.uliftFunctor.{u + 1, u}.map
      (SSet.stdSimplex.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementTerminalParameter A X Y c)) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X Y
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)))
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily]
  rw [Category.assoc, _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex_evaluation]
  rfl

lemma normalizedTensorElementUniversalFamily_augmentation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily A X Y c ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
        (homPostcompose X
          ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (Fin.last n)))) =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))) := by
  let l := SSet.uliftFunctor.{u + 1, u}.map
    (SSet.stdSimplex.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementTerminalParameter A X Y c))
  have h := _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex_augmentation_identity A X
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)))
  exact (Category.assoc _ _ _).trans ((congrArg (fun f => l ≫ f) h).trans
    (SSet.comp_const l _))

end SerrePositivity.ComplexLimits
