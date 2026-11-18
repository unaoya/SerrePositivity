module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedNoninjective
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeComponents

/-!
概要：選択集合上で非単射な作用素による実 cone の混合成分は零である。
方針：元の符号付き選択 cochain の消滅を、同じ実端点への輸送付きで使う。
規約：元の実成分と全次数を保つ。使われ方：cone pullback の非単射零分岐との比較。
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

lemma normalizedTensorConeData_hom_mixed_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hn : ¬Set.InjOn θ.toOrderHom ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) : Set (Fin (m + 1)))) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk = 0 := by
  let c' := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  have hJ := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
  have hkJ : k = 1 - ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card : ℤ) := by
    have hs := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0
    omega
  have hz := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_reindex_noninjective
    A X Y c θ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k hJ hkJ hn
  have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_mixed A X Y c' I a b k hI ha hb hk ha0 h0
  rw [hz, smul_zero] at he
  have hb' : b = ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' hJ).succ :=
    hb.trans (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.max_withoutFirst I hI h0).symm
  have hx : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c').obj a = X := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c' a = X
    rw [ha0, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_zero]
  have hy : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c').obj b =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c'.obj ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' hJ)) := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c' b = _
    rw [hb', _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_succ]
  have hzero := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k) (l := k) hx hy rfl
  exact eq_of_heq (he.trans hzero.symm)

end SerrePositivity.ComplexLimits
