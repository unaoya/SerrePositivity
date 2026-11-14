module
public import SerrePositivity.EInfinity.ComplexLimits.SimplexDataPullbackLocal
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleComponents

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementEvaluatedColumn_front {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    Fin.castSuccOrderEmb.toOrderHom.monotone.functor ⋙
      normalizedTensorElementEvaluatedColumn A X Y c =
      c ⋙ normalizedTensorElementDiagram A X Y := by
  apply CategoryTheory.Functor.hext (normalizedTensorElementEvaluatedColumn_obj_castSucc A X Y c)
  intro i j f
  exact normalizedTensorElementEvaluatedColumn_map_cast_cast A X Y c i j (leOfHom f)

lemma normalizedTensorElementEvaluatedColumn_closed_front {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (normalizedTensorElementEvaluatedColumn A X Y c ⋙ complexToClosed A)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ normalizedTensorElementDiagram A X Y ⋙ complexToClosed A) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  exact congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (F ⋙ complexToClosed A))
    (normalizedTensorElementEvaluatedColumn_front A X Y c)

lemma normalizedTensorTriangleFront_Back_hom {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (h0 : ∀ i ∈ I, τ i ≠ 0) (h2 : ∀ i ∈ I, τ i ≠ 2) :
    HEq ((normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk)
      ((normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk) := by
  have hf := simplexData_pullback_hom_eqOn
    (normalizedTensorConeSimplex A X Y c).toSimplexData
    (coneTriangleFrontIndex τ) (Fin.succOrderEmb (n + 1)).toOrderHom
    I a b k hI ha hb hk (fun i hi => coneTriangleFrontIndex_ne_zero τ i (h0 i hi))
  change HEq ((normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk)
    (((normalizedTensorConeSimplex A X Y c).pullback
      (Fin.succOrderEmb (n + 1)).toOrderHom).hom I a b k hI ha hb hk) at hf
  rw [normalizedTensorConeSimplex_tail] at hf
  have he := simplexData_pullback_hom_eqOn
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (normalizedTensorElementEvaluatedColumn A X Y c ⋙
      complexToClosed A)).toSimplexData
    (coneTriangleBackIndex τ) Fin.castSuccOrderEmb.toOrderHom
    I a b k hI ha hb hk (fun i hi => coneTriangleBackIndex_ne_two τ i (h2 i hi))
  change HEq ((normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (normalizedTensorElementEvaluatedColumn A X Y c ⋙
      complexToClosed A)).pullback Fin.castSuccOrderEmb.toOrderHom).hom
      I a b k hI ha hb hk) at he
  rw [normalizedTensorElementEvaluatedColumn_closed_front] at he
  exact hf.trans he.symm
end SerrePositivity.EInfinity.ComplexLimits
