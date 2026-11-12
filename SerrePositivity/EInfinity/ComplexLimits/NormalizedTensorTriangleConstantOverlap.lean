module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMiddle

/-!
概要：零相と二相の定値領域の全 cochain を元の pinched 単体へ同定する。
方針：元の定値引き戻し・全 cochain・全削除和を端点の等式輸送と両立させる。
規約：混合二次境界の比較は別工程。使われ方：大域評価三角形の残る HA。
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

lemma normalizedTensorTriangleFront_Pinched_zero_hom {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (h0 : ∀ i ∈ I, τ i = 0) :
    HEq ((normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk)
      ((normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk) := by
  have hf := simplexData_pullback_hom_eqOn
    (normalizedTensorConeSimplex A X Y c).toSimplexData
    (coneTriangleFrontIndex τ) (OrderHom.const _ (0 : Fin (n + 2)))
    I a b k hI ha hb hk (fun i hi => coneTriangleFrontIndex_zero τ i (h0 i hi))
  rw [simplexData_pullback_const] at hf
  let p := (normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c
  have he := simplexData_pullback_hom_eqOn p.val.toSimplexData
    (coneTriangleBackIndex τ) Fin.castSuccOrderEmb.toOrderHom I a b k hI ha hb hk
    (fun i hi => coneTriangleBackIndex_ne_two τ i (by rw [h0 i hi]; decide))
  change HEq ((normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk)
    ((p.val.pullback Fin.castSuccOrderEmb.toOrderHom).hom I a b k hI ha hb hk) at he
  have hs : p.val.pullback Fin.castSuccOrderEmb.toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) X).pullback (OrderHom.const _ (0 : Fin 1)) := p.source
  rw [hs] at he
  exact hf.trans he.symm

lemma normalizedTensorTriangleBack_Pinched_two_hom {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (h2 : ∀ i ∈ I, τ i = 2) :
    HEq ((normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
      ((normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk) := by
  have hf := simplexData_pullback_hom_eqOn
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (normalizedTensorElementEvaluatedColumn A X Y c ⋙
      complexToClosed A)).toSimplexData
    (coneTriangleBackIndex τ) (OrderHom.const _ (Fin.last (n + 1)))
    I a b k hI ha hb hk (fun i hi => coneTriangleBackIndex_two τ i (h2 i hi))
  rw [simplexData_pullback_const] at hf
  change HEq ((normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A)
      ((normalizedTensorElementEvaluatedColumn A X Y c).obj
        (Fin.last (n + 1)))).toSimplexData.pullback
        (OrderHom.const _ (0 : Fin 1))).hom I a b k hI ha hb hk) at hf
  rw [normalizedTensorElementEvaluatedColumn_obj_last] at hf
  let p := (normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c
  have he := simplexData_pullback_hom_eqOn p.val.toSimplexData
    (coneTriangleBackIndex τ) (OrderHom.const _ (Fin.last (n + 1)))
    I a b k hI ha hb hk (fun i hi => coneTriangleBackIndex_two τ i (h2 i hi))
  rw [simplexData_pullback_const, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj] at he
  exact hf.trans he.symm

end SerrePositivity.EInfinity.ComplexLimits
