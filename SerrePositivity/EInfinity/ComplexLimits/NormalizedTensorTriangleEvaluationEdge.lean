module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMixedLinear

/-!
概要：元の三角形の通常終端 cochain と実評価辺を、同じ評価射の閉成分へ回収する。
方針：元の部分集合・全添字像・実評価射と端点の等式輸送を保持する。
規約：二つの主切断の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
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


private lemma closedHom_heq {P Q P' Q' : Complex A} (hP : P = P') (hQ : Q = Q')
    (f : P ⟶ Q) (g : P' ⟶ Q') (hf : HEq f g) (k : ℤ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map f) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map g) k) := by
  cases hP
  cases hQ
  cases eq_of_heq hf
  rfl

lemma normalizedTensorTriangleBack_hom_evaluation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hat : τ a ≠ 2) (hbt : τ b = 2) :
    HEq ((normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
        ((normalizedTensorElementEvaluation A X Y).app (c.obj a))) k) := by
  let Γ := normalizedTensorElementEvaluatedColumn A X Y c
  have hab : a ≤ b := by rw [ha, hb]; exact I.min'_le _ (I.max'_mem _)
  have hx : Γ.obj (coneTriangleBackIndex τ a) =
      (normalizedTensorElementDiagram A X Y).obj (c.obj a) := by
    rw [coneTriangleBackIndex_ne_two τ a hat]
    exact normalizedTensorElementEvaluatedColumn_obj_castSucc A X Y c a
  have hy : Γ.obj (coneTriangleBackIndex τ b) = Y := by
    rw [coneTriangleBackIndex_two τ b hbt]
    exact normalizedTensorElementEvaluatedColumn_obj_last A X Y c
  have hm : ∀ (i j : Fin (n + 2)) (hi : i = a.castSucc)
      (hj : j = Fin.last (n + 1)) (h : i ≤ j),
      HEq (Γ.map (homOfLE h)) ((normalizedTensorElementEvaluation A X Y).app (c.obj a)) := by
    intro i j hi hj h
    subst i
    subst j
    exact normalizedTensorElementEvaluatedColumn_map_cast_last A X Y c a
  unfold normalizedTensorTriangleBack
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  change HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
    (Γ.map (homOfLE ((coneTriangleBackIndex τ).monotone hab)))) k) _
  exact closedHom_heq A hx hy _ _
    (hm _ _ (coneTriangleBackIndex_ne_two τ a hat)
      (coneTriangleBackIndex_two τ b hbt) _) k

lemma normalizedTensorTriangleData_hom_evaluation_edge {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha1 : τ a = 1) (hbt : τ b = 2) :
    HEq ((normalizedTensorTriangleData A X Y c τ).hom I a b 0 hI ha hb hk)
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
        ((normalizedTensorElementEvaluation A X Y).app (c.obj a)))).val := by
  have ha0 : τ a ≠ 0 := by rw [ha1]; decide
  have ha2 : τ a ≠ 2 := by rw [ha1]; decide
  have hh := normalizedTensorTriangleBack_hom_evaluation A X Y c τ I a b 0 hI ha hb hk ha2 hbt
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero] at hh
  exact (normalizedTensorTriangleData_hom_back A X Y c τ I a b 0 hI ha hb hk hbt ha0).trans hh
end SerrePositivity.EInfinity.ComplexLimits
