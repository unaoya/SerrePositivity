module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleMiddleImages
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleMiddleExtrema
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleEvaluationEdge

/-!
概要：元の主 cone cochain を同じ中央部分集合の符号付き選択 cochain へ回収する。
方針：元の切断・全添字像・端点の等式輸送を保持する。
規約：主切断の合成は別工程。使われ方：大域評価三角形の混合 HA。
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

lemma normalizedTensorTriangleData_principal_cochain {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2)
    (L : Finset (Fin (n + 1))) (hLset : L = I.filter (· ≤ _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI))
    (a b : Fin (n + 1)) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) (k : ℤ) (hL : 2 ≤ L.card)
    (haL : a = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)) (hbL : b = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hkL : k = 2 - (L.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).hom L a b k hL haL hbL hkL)
      (k.negOnePow • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c
        (I.filter (fun i => τ i = 1)) k hJ hkJ) := by
  subst ha
  subst hb
  subst hLset
  let L := I.filter (· ≤ _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI)
  let J := I.filter (fun i => τ i = 1)
  have hiI := _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_injOn_of_second_one τ I hI hs1
  have hi : Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ) (L : Set (Fin (n + 1))) := by
    intro i hi j hj he
    exact hiI (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 he
  have h0 : (0 : Fin (n + 2)) ∈ L.image (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ) := by
    refine Finset.mem_image.mpr ⟨I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI), ?_,
      _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ _ haz⟩
    exact Finset.mem_filter.mpr ⟨I.min'_mem _,
      I.min'_le _ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_mem I hI)⟩
  have he : _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst (L.image (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ)) = J :=
    _root_.SerrePositivity.ComplexLimits.withoutFirst_image_penultimate_middle τ I hI hp1 hbt
  have ht : ∀ (K : Finset (Fin (n + 1))) (hK : K.Nonempty) (hkK : k = 1 - (K.card : ℤ))
      (hKJ : K = J),
      HEq (k.negOnePow • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c K k hK hkK)
        (k.negOnePow • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hkJ) := by
    intro K hK hkK hKJ
    subst hKJ
    rfl
  have hp2 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) ≠ 2 := by rw [hp1]; decide
  refine (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ L
    (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) k hL haL hbL hkL hp2).trans ?_
  change HEq (((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c).toSimplexData.pullback
    (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ)).hom L (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
      (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) k hL haL hbL hkL) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  refine (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_mixed A X Y c _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ _ haz) h0).trans ?_
  exact ht _ _ _ he

end SerrePositivity.ComplexLimits
