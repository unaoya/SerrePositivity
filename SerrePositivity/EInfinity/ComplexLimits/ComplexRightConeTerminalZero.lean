module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeClosed

/-!
概要：実右 cone の終端への非零次数成分は零である。
方針：元の閉 augmentation の非零次数成分の零を、同じ実対象へ戻す。
規約：任意の非零整数次数。使われ方：終端 HA の非二点右切断の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexRightConeData_hom_last_zero {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) (hk0 : k ≠ 0) :
    (complexRightConeData A η).hom I a b k hI ha hb hk = 0 := by
  have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
  have hx : (complexRightConeData A η).obj a =
      s.obj ((Fin.last n).predAboveOrderHom a) := complexRightConeObj_ne_last A s X a han
  have hy : (complexRightConeData A η).obj b = X := by
    change complexRightConeObj A s X b = X
    rw [hbl, complexRightConeObj_last]
  have he := complexRightConeData_hom_last A η I a b k hI ha hb hk hbl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk0] at he
  exact eq_of_heq (he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) hx hy rfl).symm)

end SerrePositivity.EInfinity.ComplexLimits
