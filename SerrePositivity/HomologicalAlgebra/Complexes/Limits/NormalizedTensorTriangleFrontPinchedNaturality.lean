module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePieces
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeSimplexMap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementPinchedEvaluation

/-!
概要：元の三相部分単体は、退化を含む全作用素と厳密に可換である。
方針：元の cone・全 pinched 写像・通常評価余錐 join の自然性を使う。
規約：同じ実単体・時刻を保つ。使われ方：全三相データと大域三角形の接合。
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

lemma normalizedTensorTriangleFront_pullback_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ).pullback θ.toOrderHom =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) (τ.comp θ.toOrderHom) := by
  unfold _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_reindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex_pullback_map]

lemma normalizedTensorTrianglePinched_pullback_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).pullback θ.toOrderHom =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) (τ.comp θ.toOrderHom) := by
  have hn := ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).naturality θ.op) c
  change (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋m⦌)
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) =
    (((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).pullback θ) at hn
  have he := congrArg (fun p : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y) _⦋m⦌ => p.val) hn.symm
  change (((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom θ.toOrderHom)) =
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋m⦌)
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val at he
  unfold _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_reindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp]
  exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (m + 1) =>
    s.pullback (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex (τ.comp θ.toOrderHom))) he

end SerrePositivity.ComplexLimits
