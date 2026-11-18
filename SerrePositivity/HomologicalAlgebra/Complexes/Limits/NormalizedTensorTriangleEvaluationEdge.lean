module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMixedLinear

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)


private lemma closedHom_heq {P Q P' Q' : Complex A} (hP : P = P') (hQ : Q = Q')
    (f : P ⟶ Q) (g : P' ⟶ Q') (hf : HEq f g) (k : ℤ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map g) k) := by
  cases hP
  cases hQ
  cases eq_of_heq hf
  rfl

lemma normalizedTensorTriangleBack_hom_evaluation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hat : τ a ≠ 2) (hbt : τ b = 2) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj a))) k) := by
  let Γ := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c
  have hab : a ≤ b := by rw [ha, hb]; exact I.min'_le _ (I.max'_mem _)
  have hx : Γ.obj (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ a) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj a) := by
    rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ a hat]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_obj_castSucc A X Y c a
  have hy : Γ.obj (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ b) = Y := by
    rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ b hbt]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_obj_last A X Y c
  have hm : ∀ (i j : Fin (n + 2)) (hi : i = a.castSucc)
      (hj : j = Fin.last (n + 1)) (h : i ≤ j),
      HEq (Γ.map (homOfLE h)) ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj a)) := by
    intro i j hi hj h
    subst i
    subst j
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_map_cast_last A X Y c a
  unfold _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  change HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
    (Γ.map (homOfLE ((_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ).monotone hab)))) k) _
  exact _root_.SerrePositivity.ComplexLimits.closedHom_heq A hx hy _ _
    (hm _ _ (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ a hat)
      (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ b hbt) _) k

lemma normalizedTensorTriangleData_hom_evaluation_edge {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha1 : τ a = 1) (hbt : τ b = 2) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).hom I a b 0 hI ha hb hk)
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj a)))).val := by
  have ha0 : τ a ≠ 0 := by rw [ha1]; decide
  have ha2 : τ a ≠ 2 := by rw [ha1]; decide
  have hh := _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack_hom_evaluation A X Y c τ I a b 0 hI ha hb hk ha2 hbt
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero] at hh
  exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_back A X Y c τ I a b 0 hI ha hb hk hbt ha0).trans hh
end SerrePositivity.ComplexLimits
