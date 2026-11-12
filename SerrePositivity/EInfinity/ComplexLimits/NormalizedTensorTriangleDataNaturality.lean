module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleComponents
public import SerrePositivity.EInfinity.ComplexLimits.SimplexDataNoninjectiveComparison
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleFrontPinchedNaturality
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleBackNaturality
/-! 概要：三相データの全自然性。方針：像上の成分と退化を三分岐で比較。
規約：同じ元の cochain。使われ方：大域評価三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorTriangleData_pullback_map {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (normalizedTensorTriangleData A X Y c τ).pullback θ.toOrderHom =
      normalizedTensorTriangleData A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) (τ.comp θ.toOrderHom) := by
  let d := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  let σ := τ.comp θ.toOrderHom
  let s := normalizedTensorTriangleData A X Y c τ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    apply eq_of_heq; have hab : a ≤ b := by rw [ha, hb]; exact I.min'_le _ (I.max'_mem _)
    have hp : ∀ (P : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) m),
        P.pullback θ.toOrderHom = Q →
        HEq ((P.toSimplexData.pullback θ.toOrderHom).hom I a b k hI ha hb hk)
          (Q.hom I a b k hI ha hb hk) := by
      intro P Q h
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_eq (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData h) I a b k hI ha hb hk
    by_cases hi : Set.InjOn θ.toOrderHom (I : Set (Fin (m + 1)))
    · have hImg := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI
      have ham : IsLeast (I : Set (Fin (m + 1))) a := by rw [ha]; exact I.isLeast_min' _
      have hbm : IsGreatest (I : Set (Fin (m + 1))) b := by rw [hb]; exact I.isGreatest_max' _
      have haImg : θ.toOrderHom a = (I.image θ.toOrderHom).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hImg) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min θ.toOrderHom.monotone ham _
      have hbImg : θ.toOrderHom b = (I.image θ.toOrderHom).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hImg) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max θ.toOrderHom.monotone hbm _
      have hkImg : k = 2 - ((I.image θ.toOrderHom).card : ℤ) := by
        rw [Finset.card_image_of_injOn hi]
        exact hk
      have hp' : ∀ (P : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) m),
          P.pullback θ.toOrderHom = Q →
          HEq (P.hom (I.image θ.toOrderHom) (θ.toOrderHom a) (θ.toOrderHom b) k
            hImg haImg hbImg hkImg) (Q.hom I a b k hI ha hb hk) := by
        intro P Q h
        have hh := hp P Q h
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi] at hh
        exact hh
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      by_cases hb2 : τ (θ.toOrderHom b) = 2
      · by_cases ha0 : τ (θ.toOrderHom a) = 0
        · exact (normalizedTensorTriangleData_hom_pinched A X Y c τ _ _ _ k
            hImg haImg hbImg hkImg hb2 ha0).trans
            ((hp' _ _ (normalizedTensorTrianglePinched_pullback_map A X Y c τ θ)).trans
              (normalizedTensorTriangleData_hom_pinched A X Y d σ I a b k hI ha hb hk hb2 ha0).symm)
        · exact (normalizedTensorTriangleData_hom_back A X Y c τ _ _ _ k
            hImg haImg hbImg hkImg hb2 ha0).trans
            ((hp' _ _ (normalizedTensorTriangleBack_pullback_map A X Y c τ θ)).trans
              (normalizedTensorTriangleData_hom_back A X Y d σ I a b k hI ha hb hk hb2 ha0).symm)
      · exact (normalizedTensorTriangleData_hom_front A X Y c τ _ _ _ k
          hImg haImg hbImg hkImg hb2).trans
          ((hp' _ _ (normalizedTensorTriangleFront_pullback_map A X Y c τ θ)).trans
            (normalizedTensorTriangleData_hom_front A X Y d σ I a b k hI ha hb hk hb2).symm)
    · have hp' : ∀ (P : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) m),
          P.pullback θ.toOrderHom = Q →
          s.obj (θ.toOrderHom a) = P.obj (θ.toOrderHom a) →
          s.obj (θ.toOrderHom b) = P.obj (θ.toOrderHom b) →
          HEq ((s.pullback θ.toOrderHom).hom I a b k hI ha hb hk)
            (Q.hom I a b k hI ha hb hk) := by
        intro P Q h hx hy
        exact (simplexData_noninjective_pullback_hom_heq s P.toSimplexData θ.toOrderHom
          I a b k hI ha hb hk hi hx hy).trans (hp P Q h)
      by_cases hb2 : τ (θ.toOrderHom b) = 2
      · by_cases ha0 : τ (θ.toOrderHom a) = 0
        · exact (hp' _ _ (normalizedTensorTrianglePinched_pullback_map A X Y c τ θ)
            (normalizedTensorTrianglePinched_obj_zero A X Y c τ _ ha0).symm
            (normalizedTensorTrianglePinched_obj_two A X Y c τ _ hb2).symm).trans
            (normalizedTensorTriangleData_hom_pinched A X Y d σ I a b k hI ha hb hk hb2 ha0).symm
        · have hb0 : τ (θ.toOrderHom b) ≠ 0 := by rw [hb2]; decide
          exact (hp' _ _ (normalizedTensorTriangleBack_pullback_map A X Y c τ θ)
            (normalizedTensorTriangleBack_obj A X Y c τ _ ha0).symm
            (normalizedTensorTriangleBack_obj A X Y c τ _ hb0).symm).trans
            (normalizedTensorTriangleData_hom_back A X Y d σ I a b k hI ha hb hk hb2 ha0).symm
      · have ha2 : τ (θ.toOrderHom a) ≠ 2 := by
          intro ht
          apply hb2
          exact le_antisymm (Fin.le_last _) (ht ▸ τ.monotone (θ.toOrderHom.monotone hab))
        exact (hp' _ _ (normalizedTensorTriangleFront_pullback_map A X Y c τ θ)
          (normalizedTensorTriangleFront_obj A X Y c τ _ ha2).symm
          (normalizedTensorTriangleFront_obj A X Y c τ _ hb2).symm).trans
          (normalizedTensorTriangleData_hom_front A X Y d σ I a b k hI ha hb hk hb2).symm

end SerrePositivity.EInfinity.ComplexLimits
