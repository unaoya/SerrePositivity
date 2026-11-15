module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeFrontMap
public import SerrePositivity.EInfinity.Modules.RightConeTerminalZero

/-!
概要：終端を含み延長作用素で潰れる二重 cone 成分は、両側で同じ零に一致する。
方針：終端の二点辺は潰れず、それ以外の次数は非零で終端成分が零であることを使う。
規約：HA Construction 1.3.1.6・1.3.1.13、全退化作用素を許す。使われ方：全自然性の非単射分岐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_pullback_hom_terminal_not_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 3))) (a b : Fin (m + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (m + 2))
    (hn : ¬Set.InjOn (doubleConeOrderHom θ) (I : Set (Fin (m + 3)))) :
    HEq (((strictRawModuleTensorDoubleConeSimplex A X P Q c).toSimplexData.pullback
      (doubleConeOrderHom θ)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorDoubleConeSimplex A X P Q
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
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).toSimplexData
    (doubleConeOrderHom θ) I a b k hI ha hb hk hn hc
  have hr := moduleRightConeData_hom_last_zero A (dgAlgebraCategory A ((assocForget A).obj X))
    (strictRawModuleTensorConeSimplexAugmentation A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) I a b k hI ha hb hk hbl hk0
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k) (l := k)
    (strictRawModuleTensorDoubleConeSimplex_obj_reindex A X P Q c θ a)
    (strictRawModuleTensorDoubleConeSimplex_obj_reindex A X P Q c θ b) rfl
  exact (heq_of_eq hl).trans (hz.trans (heq_of_eq hr.symm))

end SerrePositivity.EInfinity.BarrattEccles
