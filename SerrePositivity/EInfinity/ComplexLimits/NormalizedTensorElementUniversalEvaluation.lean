module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversal
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorAugmentationIdentity

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementUniversalFamily_evaluation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    normalizedTensorElementUniversalFamily A X Y c ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
        (homPostcompose X ((normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)))) =
    SSet.uliftFunctor.{u + 1, u}.map
      (SSet.stdSimplex.map (normalizedTensorElementTerminalParameter A X Y c)) ≫
      normalizedTensorHomPinchedSimplex A X Y
        ((normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)))
        ((normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))) := by
  dsimp only [normalizedTensorElementUniversalFamily]
  rw [Category.assoc, normalizedTensorUniversalSimplex_evaluation]
  rfl

lemma normalizedTensorElementUniversalFamily_augmentation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    normalizedTensorElementUniversalFamily A X Y c ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
        (homPostcompose X
          ((normalizedTensorElementAugmentation A X Y).app (c.obj (Fin.last n)))) =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map (𝟙 X))) := by
  let l := SSet.uliftFunctor.{u + 1, u}.map
    (SSet.stdSimplex.map (normalizedTensorElementTerminalParameter A X Y c))
  have h := normalizedTensorUniversalSimplex_augmentation_identity A X
    ((normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)))
  exact (Category.assoc _ _ _).trans ((congrArg (fun f => l ≫ f) h).trans
    (SSet.comp_const l _))

end SerrePositivity.EInfinity.ComplexLimits
