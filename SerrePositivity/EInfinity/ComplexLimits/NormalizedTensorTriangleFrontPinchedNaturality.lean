module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePieces
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeSimplexMap
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementPinchedEvaluation

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleFront_pullback_map {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (normalizedTensorTriangleFront A X Y c τ).pullback θ.toOrderHom =
      normalizedTensorTriangleFront A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) (τ.comp θ.toOrderHom) := by
  unfold normalizedTensorTriangleFront
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, coneTriangleFrontIndex_reindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    normalizedTensorConeSimplex_pullback_map]

lemma normalizedTensorTrianglePinched_pullback_map {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (normalizedTensorTrianglePinched A X Y c τ).pullback θ.toOrderHom =
      normalizedTensorTrianglePinched A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) (τ.comp θ.toOrderHom) := by
  have hn := ConcreteCategory.congr_hom
    ((normalizedTensorElementPinchedMap A X Y).naturality θ.op) c
  change (normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋m⦌)
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) =
    (((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).pullback θ) at hn
  have he := congrArg (fun p : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y) _⦋m⦌ => p.val) hn.symm
  change (((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom θ.toOrderHom)) =
    ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋m⦌)
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val at he
  unfold normalizedTensorTrianglePinched
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, coneTriangleBackIndex_reindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp]
  exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (m + 1) =>
    s.pullback (coneTriangleBackIndex (τ.comp θ.toOrderHom))) he

end SerrePositivity.EInfinity.ComplexLimits
