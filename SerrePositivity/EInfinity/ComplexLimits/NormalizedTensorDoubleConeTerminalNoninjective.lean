module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeFrontMap
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeTerminalZero

/-!
概要：終端を含み延長作用素で潰れる二重 cone 成分は、両側で同じ零に一致する。
方針：終端の二点辺は潰れず、それ以外の次数は非零で終端成分が零であることを使う。
規約：全退化作用素を許す。使われ方：全自然性の非単射分岐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSimplex_pullback_hom_terminal_not_inj {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 3))) (a b : Fin (m + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (m + 2))
    (hn : ¬Set.InjOn (doubleConeOrderHom θ) (I : Set (Fin (m + 3)))) :
    HEq (((normalizedTensorDoubleConeSimplex A X Y c).toSimplexData.pullback
      (doubleConeOrderHom θ)).hom I a b k hI ha hb hk)
      ((normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk) := by
  have hc : I.card ≠ 2 := by
    intro hc
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hn hc
      (show IsLeast (I : Set (Fin (m + 3))) a by rw [ha]; exact I.isLeast_min' _)
      (show IsGreatest (I : Set (Fin (m + 3))) b by rw [hb]; exact I.isGreatest_max' _)
    have hal : a = Fin.last (m + 2) := (doubleConeOrderHom_eq_last_iff θ a).mp
      (he.trans (hbl ▸ doubleConeOrderHom_last θ))
    have han : a ≠ Fin.last (m + 2) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
    exact han hal
  have hk0 : k ≠ 0 := by omega
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj
    (normalizedTensorDoubleConeSimplex A X Y c).toSimplexData
    (doubleConeOrderHom θ) I a b k hI ha hb hk hn hc
  have hr := complexRightConeData_hom_last_zero A
    (normalizedTensorConeSimplexAugmentation A X Y
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) I a b k hI ha hb hk hbl hk0
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k) (l := k)
    (normalizedTensorDoubleConeSimplex_obj_reindex A X Y c θ a)
    (normalizedTensorDoubleConeSimplex_obj_reindex A X Y c θ b) rfl
  exact (heq_of_eq hl).trans (hz.trans (heq_of_eq hr.symm))

end SerrePositivity.EInfinity.ComplexLimits
