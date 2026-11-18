module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeOrdinaryPullbackZero
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeOrdinaryZero
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：実 cone の全通常成分は、始点付き単射の制限と整合する。
方針：零次成分は同じ実辺へ、他の次数は両側の零成分へ戻す。
規約：元の全次数と端点を保持する。使われ方：全データの単射 pullback の一致。
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
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk) := by
  by_cases hk0 : k = 0
  · subst hk0
    exact strictRawModuleTensorConeData_pullback_hom_ordinary_zero A X P Q c e I a b hI ha hb hk ha0
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom
  have hi : Set.InjOn α (I : Set (Fin (m + 2))) := (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.prepend_injective e).injOn
  have hII := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI
  have haI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
    (show IsLeast (I : Set (Fin (m + 2))) a by rw [ha]; exact I.isLeast_min' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hbI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
    (show IsGreatest (I : Set (Fin (m + 2))) b by rw [hb]; exact I.isGreatest_max' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hkI : k = 2 - ((I.image α).card : ℤ) := by
    rw [Finset.card_image_of_injOn hi]
    exact hk
  have hc : I.card ≠ 2 := by intro h; apply hk0; omega
  have hcI : (I.image α).card ≠ 2 := by rw [Finset.card_image_of_injOn hi]; exact hc
  have haI0 : α a ≠ 0 := fun h => ha0 ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.prepend_eq_zero_iff e a).mp h)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have hl := strictRawModuleTensorConeData_hom_ordinary_zero A X P Q c (I.image α)
    (α a) (α b) k hII haI hbI hkI haI0 hcI
  have hr := strictRawModuleTensorConeData_hom_ordinary_zero A X P Q
    ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
    I a b k hI ha hb hk ha0 hc
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k) (l := k)
    (strictRawModuleTensorConeData_obj_prepend A X P Q c e a)
    (strictRawModuleTensorConeData_obj_prepend A X P Q c e b) rfl
  exact (heq_of_eq hl).trans (hz.trans (heq_of_eq hr.symm))

end SerrePositivity.EInfinity.BarrattEccles
