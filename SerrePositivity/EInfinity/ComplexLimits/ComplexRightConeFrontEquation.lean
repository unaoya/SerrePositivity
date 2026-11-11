module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeFront
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRecoverIndex

/-!
概要：実右 cone の終端を含まない全有限集合で、元の HA 方程式を保持する。
方針：元の単体への前面制限の厳密な一致から、同じ集合へ方程式を戻す。
規約：任意の複体単体と指定 augmentation。使われ方：終端成分の方程式への還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexRightConeData_equation_without_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X) (I : Finset (Fin (n + 2)))
    (hl : Fin.last (n + 1) ∉ I) : (complexRightConeData A η).Equation I := by
  have h := (complexRightConeData A η).equation_image_of_pullback
    Fin.castSuccOrderEmb.toOrderHom s (complexRightConeData_front A η)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I) (Fin.castSucc_injective _).injOn
  have hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I).image Fin.castSuccOrderEmb.toOrderHom = I := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I).image Fin.castSucc = I
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withoutLast, Finset.erase_eq_of_notMem hl]
  simpa only [hi] using h

end SerrePositivity.EInfinity.ComplexLimits
