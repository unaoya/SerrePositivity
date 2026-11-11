module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorUniversalAugmentationVertex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedAugmentation

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_augmentation_vertex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    (homPostcompose X ((normalizedTensorElementAugmentation A X Y).app (c.obj (J.max' hJ)))).f 0
      (normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega)) =
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))).val := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A X ((normalizedTensorElementDiagram A X Y).obj (c.obj i)) 0),
      (homPostcompose X ((normalizedTensorElementAugmentation A X Y).app (c.obj j))).f 0
        (cast (congrArg (fun z => (GradedHom A X
          ((normalizedTensorElementDiagram A X Y).obj (c.obj z)) 0 : Type u)) h) v) =
      (homPostcompose X ((normalizedTensorElementAugmentation A X Y).app (c.obj i))).f 0 v := by
    intro i j h v
    subst j
    rfl
  have hcard : J.card = J.card - 1 + 1 := by omega
  have hz := normalizedTensorElementUniversalLinear_augmentation_vertex A X Y
    ((SimplexCategory.toCat.map (normalizedTensorElementSelection J hJ)).toFunctor ⋙ c)
    Finset.univ Finset.univ_nonempty
    (by simpa only [Finset.card_univ, Fintype.card_fin, ← hcard] using hc)
  exact (ht _ _ (normalizedTensorElementSelection_last J hJ)
    (normalizedTensorElementSelectedCochain A X Y c J 0 hJ (by omega))).trans hz

lemma normalizedTensorElementSelectedCochainAtMax_augmentation_compose_vertex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    compose A (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
      ((normalizedTensorElementAugmentation A X Y).app (c.obj (J.max' hJ))))).val
      (normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega)) (add_zero 0) =
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))).val := by
  rw [complexPostcompose_graded]
  exact normalizedTensorElementSelectedCochainAtMax_augmentation_vertex A X Y c J hJ hc

end SerrePositivity.EInfinity.ComplexLimits
