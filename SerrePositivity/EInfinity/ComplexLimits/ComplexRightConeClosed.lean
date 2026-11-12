module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：実右 cone の指定終端への全成分の微分は零である。
方針：同じ閉 augmentation の斉次成分へ移し、零次の閉性と他次数の零を使う。
規約：全有限集合・全次数。使われ方：終端 HA 方程式の左辺。
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

lemma complexRightConeData_differential_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    differential A ((complexRightConeData A η).hom I a b k hI ha hb hk) = 0 := by
  have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
  have hx : (complexRightConeData A η).obj a =
      s.obj ((Fin.last n).predAboveOrderHom a) := complexRightConeObj_ne_last A s X a han
  have hy : (complexRightConeData A η).obj b = X := by
    change complexRightConeObj A s X b = X
    rw [hbl, complexRightConeObj_last]
  have he := complexRightConeData_hom_last A η I a b k hI ha hb hk hbl
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy rfl _ _ he
  have hz : differential A
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map (η.app ((Fin.last n).predAboveOrderHom a))) k)
        = 0 := by
    by_cases hk0 : k = 0
    · subst hk0
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero]
      exact (ComplexSimplexAugmentation.cycle A η _).property
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk0]
      exact map_zero _
  exact eq_of_heq (hd.trans ((heq_of_eq hz).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k + 1) (l := k + 1) hx hy rfl).symm))

end SerrePositivity.EInfinity.ComplexLimits
