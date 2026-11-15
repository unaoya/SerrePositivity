module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeErasedLast
public import SerrePositivity.EInfinity.ComplexLimits.ConeBoundarySum
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRhs

/-!
概要：始点と終端を含む実 cone の線形境界を、同じ普遍 cochain の内部削除和へ移す。
方針：全内部点を後続元で再添字付けし、各削除成分と符号を同じ座標へ同定する。
規約：同じ全有限和を保持する。使われ方：終端切断を戻す混合 HA 方程式の右辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_linearBoundary_reindex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) :
    (strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k =
      ∑ j : withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val •
          (strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j.val.succ) a b (k + 1)
        else 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.linearBoundary
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I 0 (Fin.last (n + 1)) := by rw [ha0, hbl]
  rw [hi, sum_interior_zero_last]
  simp only [sign_succ]

lemma strictRawModuleTensorConeData_linearBoundary_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1))
    (h0 : 0 ∈ I) (hJ : 2 ≤ (withoutFirst I).card)
    (hkJ : k = 1 - ((withoutFirst I).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k)
      (∑ j : withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val • ((k + 1).negOnePow •
          (strictRawModuleTensorElementLinear A X P Q c).val.component
            ((withoutFirst I).erase j.val) (k + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ j.property)
            (by have := Finset.card_erase_add_one j.property; omega)) else 0) := by
  have hx : (strictRawModuleTensorConeData A X P Q c).obj a = (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) := by
    change strictRawModuleTensorConeObj A X P Q c a = _
    rw [ha0, strictRawModuleTensorConeObj_zero]
  have hy : (strictRawModuleTensorConeData A X P Q c).obj b =
      (strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)) := by
    change strictRawModuleTensorConeObj A X P Q c b = _
    rw [hbl]
    exact strictRawModuleTensorConeObj_succ A X P Q c (Fin.last n)
  rw [strictRawModuleTensorConeData_linearBoundary_reindex A X P Q c I a b k ha0 hbl]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_heq_of_obj_eq hx hy
  intro j
  by_cases hj : j.val < Fin.last n
  · simp only [ite_eq_left hj]
    have he := strictRawModuleTensorConeData_erased_succ_mixed_last A X P Q c I a b k hI ha hb hk
      ha0 hbl h0 j.val (by simpa only [withoutFirst, Finset.mem_filter, Finset.mem_univ,
        true_and] using j.property) (by rw [hbl]; exact Fin.succ_lt_succ_iff.mpr hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ j.property)
      (by have := Finset.card_erase_add_one j.property; omega)
    have ht : ∀ (x y x' y' : RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (hx : x = x') (hy : y = y')
        (v : GradedHom A x y (k + 1)) (w : GradedHom A x' y' (k + 1)),
        HEq v w → HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val • v)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val • w) := by
      intro x y x' y' hx hy v w hv
      subst x'
      subst y'
      cases eq_of_heq hv
      rfl
    exact ht _ _ _ _ hx hy _ _ he
  · simp only [ite_eq_right hj]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl

end SerrePositivity.EInfinity.BarrattEccles
