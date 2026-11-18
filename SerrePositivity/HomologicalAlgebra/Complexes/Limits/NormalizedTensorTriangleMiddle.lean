module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SimplexDataPullbackLocal
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleComponents

/-!
概要：元の評価列の全前面と、三相単体の中央相の二表示の全 cochain を同定する。
方針：全成分・全切断・微分の比較を端点の等式輸送と両立させる。
規約：元の実単体と同じ対象・次数を保持する。使われ方：大域評価三角形の全 HA。
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

lemma normalizedTensorElementEvaluatedColumn_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    Fin.castSuccOrderEmb.toOrderHom.monotone.functor ⋙
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c =
      c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y := by
  apply CategoryTheory.Functor.hext (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_obj_castSucc A X Y c)
  intro i j f
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_map_cast_cast A X Y c i j (leOfHom f)

lemma normalizedTensorElementEvaluatedColumn_closed_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  exact congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (F ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_front A X Y c)

lemma normalizedTensorTriangleFront_Back_hom {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (h0 : ∀ i ∈ I, τ i ≠ 0) (h2 : ∀ i ∈ I, τ i ≠ 2) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk) := by
  have hf := _root_.SerrePositivity.ComplexLimits.simplexData_pullback_hom_eqOn
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c).toSimplexData
    (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ) (Fin.succOrderEmb (n + 1)).toOrderHom
    I a b k hI ha hb hk (fun i hi => _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ i (h0 i hi))
  change HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk)
    (((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c).pullback
      (Fin.succOrderEmb (n + 1)).toOrderHom).hom I a b k hI ha hb hk) at hf
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex_tail] at hf
  have he := _root_.SerrePositivity.ComplexLimits.simplexData_pullback_hom_eqOn
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c ⋙
      _root_.SerrePositivity.ComplexLimits.complexToClosed A)).toSimplexData
    (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) Fin.castSuccOrderEmb.toOrderHom
    I a b k hI ha hb hk (fun i hi => _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ i (h2 i hi))
  change HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c ⋙
      _root_.SerrePositivity.ComplexLimits.complexToClosed A)).pullback Fin.castSuccOrderEmb.toOrderHom).hom
      I a b k hI ha hb hk) at he
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_closed_front] at he
  exact hf.trans he.symm
end SerrePositivity.ComplexLimits
