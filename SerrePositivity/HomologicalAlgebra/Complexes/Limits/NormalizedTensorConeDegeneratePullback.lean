module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConePrependInjOn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeDegenerateMixed

/-!
概要：実 cone の混合成分の非単射零分岐は、元の作用素で制限した cone の成分と一致する。
方針：尾の非単射性と三点以上の濃度を確認し、同じ二つの零成分を端点付きで比較する。
規約：元の pullback と同じ実制限列を保持する。使われ方：全退化自然性。
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

lemma normalizedTensorConeData_obj_prepend_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma normalizedTensorConeData_pullback_hom_mixed_not_inj {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hn : ¬Set.InjOn θ.toOrderHom ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) : Set (Fin (m + 1)))) :
    HEq (((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
        I a b k hI ha hb hk) := by
  have hni : ¬Set.InjOn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) (I : Set (Fin (m + 2))) :=
    fun h => hn ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.prepend_injOn_iff θ.toOrderHom I).mp h)
  have hc : I.card ≠ 2 := by
    intro hc
    have hcard : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card ≤ 1 := by
      have hs := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0
      omega
    apply hn
    intro i hi j hj _
    exact (Finset.card_le_one.mp hcard) i hi j hj
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) I a b k hI ha hb hk hni hc
  have hr := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_mixed_reindex_noninjective
    A X Y c θ I a b k hI ha hb hk ha0 h0 hn
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k) (l := k)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_obj_prepend_map A X Y c θ a)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_obj_prepend_map A X Y c θ b) rfl
  exact (heq_of_eq hl).trans (hz.trans (heq_of_eq hr.symm))

end SerrePositivity.ComplexLimits
