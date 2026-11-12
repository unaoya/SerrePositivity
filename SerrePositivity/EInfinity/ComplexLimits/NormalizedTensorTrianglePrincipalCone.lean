module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTriangleMiddleImages
public import SerrePositivity.EInfinity.ComplexLimits.ConeTriangleMiddleExtrema
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleEvaluationEdge

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_principal_cochain {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2)
    (L : Finset (Fin (n + 1))) (hLset : L = I.filter (· ≤ ConeHeadIndex.penultimate I hI))
    (a b : Fin (n + 1)) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = ConeHeadIndex.penultimate I hI) (k : ℤ) (hL : 2 ≤ L.card)
    (haL : a = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)) (hbL : b = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hkL : k = 2 - (L.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq ((normalizedTensorTriangleData A X Y c τ).hom L a b k hL haL hbL hkL)
      (k.negOnePow • normalizedTensorElementSelectedCochainAtMax A X Y c
        (I.filter (fun i => τ i = 1)) k hJ hkJ) := by
  subst ha
  subst hb
  subst hLset
  let L := I.filter (· ≤ ConeHeadIndex.penultimate I hI)
  let J := I.filter (fun i => τ i = 1)
  have hiI := coneTriangleFrontIndex_injOn_of_second_one τ I hI hs1
  have hi : Set.InjOn (coneTriangleFrontIndex τ) (L : Set (Fin (n + 1))) := by
    intro i hi j hj he
    exact hiI (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 he
  have h0 : (0 : Fin (n + 2)) ∈ L.image (coneTriangleFrontIndex τ) := by
    refine Finset.mem_image.mpr ⟨I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI), ?_,
      coneTriangleFrontIndex_zero τ _ haz⟩
    exact Finset.mem_filter.mpr ⟨I.min'_mem _,
      I.min'_le _ (ConeHeadIndex.penultimate_mem I hI)⟩
  have he : ConeHeadIndex.withoutFirst (L.image (coneTriangleFrontIndex τ)) = J :=
    withoutFirst_image_penultimate_middle τ I hI hp1 hbt
  have ht : ∀ (K : Finset (Fin (n + 1))) (hK : K.Nonempty) (hkK : k = 1 - (K.card : ℤ))
      (hKJ : K = J),
      HEq (k.negOnePow • normalizedTensorElementSelectedCochainAtMax A X Y c K k hK hkK)
        (k.negOnePow • normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hkJ) := by
    intro K hK hkK hKJ
    subst hKJ
    rfl
  have hp2 : τ (ConeHeadIndex.penultimate I hI) ≠ 2 := by rw [hp1]; decide
  refine (normalizedTensorTriangleData_hom_front A X Y c τ L
    (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (ConeHeadIndex.penultimate I hI) k hL haL hbL hkL hp2).trans ?_
  change HEq (((normalizedTensorConeSimplex A X Y c).toSimplexData.pullback
    (coneTriangleFrontIndex τ)).hom L (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
      (ConeHeadIndex.penultimate I hI) k hL haL hbL hkL) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  refine (normalizedTensorConeData_hom_mixed A X Y c _ _ _ _ _ _ _ _
    (coneTriangleFrontIndex_zero τ _ haz) h0).trans ?_
  exact ht _ _ _ he

end SerrePositivity.EInfinity.ComplexLimits
