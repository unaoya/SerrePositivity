module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedNoninjective
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeComponents

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
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open ConeHeadIndex
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_mixed_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hn : ¬Set.InjOn θ.toOrderHom ((withoutFirst I) : Set (Fin (m + 1)))) :
    (strictRawModuleTensorConeData A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk = 0 := by
  let c' := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  have hJ := withoutFirst_nonempty hI h0
  have hkJ : k = 1 - ((withoutFirst I).card : ℤ) := by
    have hs := card_withoutFirst I h0
    omega
  have hz := strictRawModuleTensorElementSelectedCochainAtMax_reindex_noninjective
    A X P Q c θ (withoutFirst I) k hJ hkJ hn
  have he := strictRawModuleTensorConeData_hom_mixed A X P Q c' I a b k hI ha hb hk ha0 h0
  rw [hz, smul_zero] at he
  have hb' : b = ((withoutFirst I).max' hJ).succ :=
    hb.trans (max_withoutFirst I hI h0).symm
  have hx : (strictRawModuleTensorConeData A X P Q c').obj a = ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P) := by
    change strictRawModuleTensorConeObj A X P Q c' a = _
    rw [ha0, strictRawModuleTensorConeObj_zero]
  have hy : (strictRawModuleTensorConeData A X P Q c').obj b =
      ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c'.obj ((withoutFirst I).max' hJ))) := by
    change strictRawModuleTensorConeObj A X P Q c' b = _
    rw [hb', strictRawModuleTensorConeObj_succ]
  have hzero := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k) (l := k) hx hy rfl
  exact eq_of_heq (he.trans hzero.symm)

end SerrePositivity.EInfinity.BarrattEccles
