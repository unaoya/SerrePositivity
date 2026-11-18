module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConePrependObjects
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeOrdinaryClosed

/-!
概要：実 cone の通常零次成分は、始点付き単射の制限と整合する。
方針：両成分を元の閉 frame 辺へ戻し、同じ元の添字の射を照合する。
規約：元の実辺・端点を保持する。使われ方：全データの単射 pullback の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary_zero {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b 0 hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b 0 hI ha hb hk) := by
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom
  have hi : Set.InjOn α (I : Set (Fin (m + 2))) := (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.prepend_injective e).injOn
  have hII := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI
  have haI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
    (show IsLeast (I : Set (Fin (m + 2))) a by rw [ha]; exact I.isLeast_min' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hbI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
    (show IsGreatest (I : Set (Fin (m + 2))) b by rw [hb]; exact I.isGreatest_max' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hkI : (0 : ℤ) = 2 - ((I.image α).card : ℤ) := by
    rw [Finset.card_image_of_injOn hi]
    exact hk
  have hab : a ≤ b := by rw [ha, hb]; exact I.min'_le _ (I.max'_mem _)
  have hb0 : b ≠ 0 := by
    intro h
    exact ha0 (Fin.le_zero_iff.mp (h ▸ hab))
  have haI0 : α a ≠ 0 := fun h => ha0 ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.prepend_eq_zero_iff e a).mp h)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have hl := strictRawModuleTensorConeData_hom_ordinary_closed A X P Q c (I.image α)
    (α a) (α b) hII haI hbI hkI haI0 (α.monotone hab)
  have hr := strictRawModuleTensorConeData_hom_ordinary_closed A X P Q
    ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
    I a b hI ha hb hk ha0 hab
  have ht : ∀ (i j i' j' : Fin (n + 1)) (hi : i = i') (hj : j = j')
      (hij : i ≤ j) (hij' : i' ≤ j'),
      HEq (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map (c.map (homOfLE hij)))).val
        (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map (c.map (homOfLE hij')))).val := by
    intro i j i' j' hi hj hij hij'
    subst i'
    subst j'
    rfl
  exact hl.trans ((ht _ _ _ _ (_root_.SerrePositivity.ComplexLimits.coneTailOrderHom_prepend_of_ne_zero e a ha0)
    (_root_.SerrePositivity.ComplexLimits.coneTailOrderHom_prepend_of_ne_zero e b hb0) _ _).trans hr.symm)

end SerrePositivity.EInfinity.BarrattEccles
