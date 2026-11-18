module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexRightConeData

/-!
概要：実右 cone の通常成分と終端成分を、元のデータと指定 augmentation へ回収する。
方針：終点の二分岐を評価し、対象の移送を異種等号で保持する。
規約：全次数の同じ成分。使われ方：前面の回収と終端 HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexRightConeData_hom_ordinary {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : _root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation A s X)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b ≠ Fin.last (n + 1)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.complexRightConeData A η).hom I a b k hI ha hb hk)
      ((s.toSimplexData.pullback (Fin.last n).predAboveOrderHom).hom I a b k hI ha hb hk) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.complexRightConeData]
  rw [dite_eq_right hbl]
  exact cast_heq _ _

lemma complexRightConeData_hom_last {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : _root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation A s X)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.complexRightConeData A η).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (η.app ((Fin.last n).predAboveOrderHom a))) k) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.complexRightConeData]
  rw [dite_eq_left hbl]
  exact cast_heq _ _

end SerrePositivity.ComplexLimits
