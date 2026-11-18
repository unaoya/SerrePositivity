module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConePrependInjOn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedInjOn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeComponents

/-!
概要：元の実 cone の集合上単射な pullback と、制限した元の列の cone の混合成分を比較する。
方針：引き戻しを像の成分へ戻し、同じ選択 cochain の像の再添字の式を適用する。
規約：元の実成分・符号・端点を保持する。
使われ方：任意終端への制限と全混合 HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_pullback_hom_mixed_of_injOn {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hθ : Set.InjOn θ.toOrderHom ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) : Set (Fin (m + 1)))) :
    HEq (((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk) := by
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom
  have hi : Set.InjOn α (I : Set (Fin (m + 2))) := (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.prepend_injOn_iff θ.toOrderHom I).mpr hθ
  have hII := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI
  have haI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
    (show IsLeast (I : Set (Fin (m + 2))) a by rw [ha]; exact I.isLeast_min' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hbI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
    (show IsGreatest (I : Set (Fin (m + 2))) b by rw [hb]; exact I.isGreatest_max' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hkI : k = 2 - ((I.image α).card : ℤ) := by
    rw [Finset.card_image_of_injOn hi]
    exact hk
  have haI0 : α a = 0 := by rw [ha0]; rfl
  have h0I : (0 : Fin (n + 2)) ∈ I.image α := Finset.mem_image.mpr ⟨0, h0, rfl⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have hl := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_mixed A X Y c (I.image α) (α a) (α b) k
    hII haI hbI hkI haI0 h0I
  have hr := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_mixed A X Y
    ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
    I a b k hI ha hb hk ha0 h0
  have hJ := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
  have hkJ : k = 1 - ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card : ℤ) := by
    have hs := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0
    omega
  have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_image_reindex_of_injOn_smul
    A X Y c θ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k hJ hkJ hθ k.negOnePow
  have ht : ∀ (K L : Finset (Fin (n + 1))) (h : K = L)
      (hK : K.Nonempty) (hL : L.Nonempty)
      (hkK : k = 1 - (K.card : ℤ)) (hkL : k = 1 - (L.card : ℤ)),
      HEq (k.negOnePow • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c K k hK hkK)
        (k.negOnePow • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c L k hL hkL) := by
    intro K L h hK hL hkK hkL
    subst L
    rfl
  have hkK : k = 1 - ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst (I.image α)).card : ℤ) := by
    have hs := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst (I.image α) h0I
    omega
  have hs := ht _ _ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_image_prepend_map θ.toOrderHom I)
    (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hII h0I) (hJ.image θ.toOrderHom) hkK
    (by rw [Finset.card_image_of_injOn hθ]; exact hkJ)
  exact hl.trans (hs.trans (he.trans hr.symm))

end SerrePositivity.ComplexLimits
