module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorUniversalAugmentationVertex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedAugmentation

/-!
概要：一点選択の元の cochain は、同じ最大点の実 augmentation で恒等 cochain へ戻る。
方針：添字等式の輸送と後合成を両立させ、同じ選択列の一点普遍成分を使う。
規約：元の実辺を保持する。使われ方：二重 cone の三点方程式。
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

lemma normalizedTensorElementSelectedCochainAtMax_augmentation_vertex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (J.max' hJ)))).f 0
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega)) =
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))).val := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)) 0),
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj j))).f 0
        (cast (congrArg (fun z => (GradedHom A X
          ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj z)) 0 : Type u)) h) v) =
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj i))).f 0 v := by
    intro i j h v
    subst j
    rfl
  have hcard : J.card = J.card - 1 + 1 := by omega
  have hz := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear_augmentation_vertex A X Y
    ((SimplexCategory.toCat.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection J hJ)).toFunctor ⋙ c)
    Finset.univ Finset.univ_nonempty
    (by simpa only [Finset.card_univ, Fintype.card_fin, ← hcard] using hc)
  exact (ht _ _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection_last J hJ)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochain A X Y c J 0 hJ (by omega))).trans hz

lemma normalizedTensorElementSelectedCochainAtMax_augmentation_compose_vertex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (J.max' hJ))))).val
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega)) (add_zero 0) =
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))).val := by
  rw [_root_.SerrePositivity.ComplexLimits.complexPostcompose_graded]
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_augmentation_vertex A X Y c J hJ hc

end SerrePositivity.ComplexLimits
