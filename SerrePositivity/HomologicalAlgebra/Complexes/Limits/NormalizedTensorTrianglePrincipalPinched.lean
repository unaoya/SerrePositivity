module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleMiddleImages
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleMiddleExtrema
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMiddleSums

/-!
概要：元の主 pinched cochain を同じ中央部分集合の元の線形成分へ回収する。
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

lemma normalizedTensorTrianglePinched_principal_cochain {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2)
    (R : Finset (Fin (n + 1))) (hRset : R = I.filter (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI ≤ ·))
    (a b : Fin (n + 1)) (ha : a = _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI)
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (k : ℤ) (hR : 2 ≤ R.card)
    (haR : a = R.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)) (hbR : b = R.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hkR : k = 2 - (R.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).hom R a b k hR haR hbR hkR)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
          (I.filter (fun i => τ i = 1)) k hJ hkJ) := by
  subst ha
  subst hb
  subst hRset
  let R := I.filter (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI ≤ ·)
  let J := I.filter (fun i => τ i = 1)
  let p := (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c
  have hiI := _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_injOn_of_penultimate_one τ I hI hp1
  have hi : Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) (R : Set (Fin (n + 1))) := by
    intro i hi j hj he
    exact hiI (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 he
  have hl : Fin.last (n + 1) ∈ R.image (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) := by
    refine Finset.mem_image.mpr ⟨I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI), ?_,
      _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ _ hbt⟩
    exact Finset.mem_filter.mpr ⟨I.max'_mem _,
      I.le_max' _ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second_mem I hI)⟩
  have he : R.image (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast
      (R.image (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ)) hl
    rw [_root_.SerrePositivity.ComplexLimits.withoutLast_image_second_middle τ I hI hs1 haz] at h
    exact h.symm
  have hm : J.min' hJ = _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI := _root_.SerrePositivity.ComplexLimits.middle_min_eq_second τ I hI hs1 haz
  have hs2 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) ≠ 2 := by rw [hs1]; decide
  change HEq ((p.val.toSimplexData.pullback (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ)).hom
    R (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) k hR haR hbR hkR) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq p J k hJ hkJ
  refine HEq.trans ?_ hc.symm
  exact p.val.toSimplexData.hom_heq_of_indices_degree he
    ((_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ _ hs2).trans (congrArg Fin.castSucc hm.symm))
    (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ _ hbt) rfl

end SerrePositivity.ComplexLimits
