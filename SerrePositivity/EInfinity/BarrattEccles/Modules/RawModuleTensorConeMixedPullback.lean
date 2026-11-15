module
public import SerrePositivity.EInfinity.ComplexLimits.ConePrependIndex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedImageReindex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeComponents

/-!
概要：元の実 cone の単射 pullback と、制限した元の列の cone の混合成分を比較する。
方針：引き戻しを像の成分へ戻し、同じ選択 cochain の像の再添字の式を適用する。
規約：元の実成分・符号・端点を保持する。
使われ方：任意終端への制限と全混合 HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_mixed {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk) := by
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom
  have hi : Set.InjOn α (I : Set (Fin (m + 2))) := (prepend_injective e).injOn
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
  have hl := strictRawModuleTensorConeData_hom_mixed A X P Q c (I.image α) (α a) (α b) k
    hII haI hbI hkI haI0 h0I
  have hr := strictRawModuleTensorConeData_hom_mixed A X P Q
    ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
    I a b k hI ha hb hk ha0 h0
  have hJ := withoutFirst_nonempty hI h0
  have hkJ : k = 1 - ((withoutFirst I).card : ℤ) := by
    have hs := card_withoutFirst I h0
    omega
  have he := strictRawModuleTensorElementSelectedCochainAtMax_image_reindex_smul
    A X P Q c e (withoutFirst I) k hJ hkJ k.negOnePow
  have ht : ∀ (K L : Finset (Fin (n + 1))) (h : K = L)
      (hK : K.Nonempty) (hL : L.Nonempty)
      (hkK : k = 1 - (K.card : ℤ)) (hkL : k = 1 - (L.card : ℤ)),
      HEq (k.negOnePow • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c K k hK hkK)
        (k.negOnePow • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c L k hL hkL) := by
    intro K L h hK hL hkK hkL
    subst L
    rfl
  have hkK : k = 1 - ((withoutFirst (I.image α)).card : ℤ) := by
    have hs := card_withoutFirst (I.image α) h0I
    omega
  have hs := ht _ _ (withoutFirst_image_prepend e I)
    (withoutFirst_nonempty hII h0I) (hJ.image e) hkK
    (by rw [Finset.card_image_of_injective _ e.injective]; exact hkJ)
  exact hl.trans (hs.trans (he.trans hr.symm))

end SerrePositivity.EInfinity.BarrattEccles
