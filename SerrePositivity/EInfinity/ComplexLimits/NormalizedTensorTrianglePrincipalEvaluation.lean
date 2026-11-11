module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePrincipalCone
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedEvaluation

/-!
概要：元の主切断の評価・単位合成と符号から、同じ中央相の全切断和を比較する。
方針：元の二つの切断・実評価成分・全添字と次数を保持する。
規約：全二次境界と混合 HA は別工程。使われ方：大域評価三角形の実三相単体。
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

lemma normalizedTensorTriangleData_principal_composite {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2)
    (L : Finset (Fin (n + 1))) (hLset : L = I.filter (· ≤ ConeHeadIndex.penultimate I hI))
    (R : Finset (Fin (n + 1))) (k : ℤ)
    (hL : 2 ≤ L.card) (hLa : I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hLp : ConeHeadIndex.penultimate I hI = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hkL : k = 2 - (L.card : ℤ)) (hR : 2 ≤ R.card)
    (hRp : ConeHeadIndex.penultimate I hI = R.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hRb : I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) = R.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hkR : (0 : ℤ) = 2 - (R.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq (compose A
      ((normalizedTensorTriangleData A X Y c τ).hom R (ConeHeadIndex.penultimate I hI)
        (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) 0 hR hRp hRb hkR)
      ((normalizedTensorTriangleData A X Y c τ).hom L (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
        (ConeHeadIndex.penultimate I hI) k hL hLa hLp hkL) (add_zero k))
      (k.negOnePow • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
        ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
          (I.filter (fun i => τ i = 1)) k hJ hkJ) := by
  let J := I.filter (fun i => τ i = 1)
  have hm : J.max' hJ = ConeHeadIndex.penultimate I hI :=
    middle_max_eq_penultimate τ I hI hp1 hbt
  have hl := normalizedTensorTriangleData_principal_cochain A X Y c τ I hI hs1 hp1 haz hbt
    L hLset _ _ rfl rfl k hL hLa hLp hkL hJ hkJ
  have hr := normalizedTensorTriangleData_hom_evaluation_edge A X Y c τ R
    (ConeHeadIndex.penultimate I hI) (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) hR hRp hRb hkR hp1 hbt
  have he : HEq (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
      ((normalizedTensorElementEvaluation A X Y).app (c.obj (ConeHeadIndex.penultimate I hI))))).val
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
        ((normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ))))).val := by
    rw [hm]
  have hx : (normalizedTensorTriangleData A X Y c τ).obj (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = X := by
    change normalizedTensorTriangleObj A X Y c τ _ = X
    simp only [normalizedTensorTriangleObj, haz, ↓reduceIte]
  have hy : (normalizedTensorTriangleData A X Y c τ).obj (ConeHeadIndex.penultimate I hI) =
      (normalizedTensorElementDiagram A X Y).obj (c.obj (J.max' hJ)) := by
    change normalizedTensorTriangleObj A X Y c τ _ = _
    have hp0 : τ (ConeHeadIndex.penultimate I hI) ≠ 0 := by rw [hp1]; decide
    have hp2 : τ (ConeHeadIndex.penultimate I hI) ≠ 2 := by rw [hp1]; decide
    simp only [normalizedTensorTriangleObj, hp0, hp2, ↓reduceIte]
    exact congrArg (fun i => (normalizedTensorElementDiagram A X Y).obj (c.obj i)) hm.symm
  have hz : (normalizedTensorTriangleData A X Y c τ).obj (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = Y := by
    change normalizedTensorTriangleObj A X Y c τ _ = Y
    simp [normalizedTensorTriangleObj, hbt]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq hx hy hz rfl rfl rfl _ _ _ _ (hr.trans he) hl
    (add_zero k) (add_zero k)
  exact hc.trans (heq_of_eq
    (normalizedTensorElementSelectedCochainAtMax_evaluation_compose A X Y c J k hJ hkJ k.negOnePow))

end SerrePositivity.EInfinity.ComplexLimits
