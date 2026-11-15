module
public import SerrePositivity.EInfinity.Modules.RightConeFront
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRecoverIndex

/-!
概要：実加群右 cone の終端を含まない全有限集合で、元の HA 方程式を保持する。
方針：元の単体への前面制限の厳密な一致から、同じ集合へ方程式を戻す。
規約：HA Construction 1.3.1.6・1.3.1.13、任意の複体単体と指定 augmentation。使われ方：終端成分の方程式への還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_equation_without_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) (I : Finset (Fin (n + 2)))
    (hl : Fin.last (n + 1) ∉ I) : (moduleRightConeData A D η).Equation I := by
  have h := (moduleRightConeData A D η).equation_image_of_pullback
    Fin.castSuccOrderEmb.toOrderHom s (moduleRightConeData_front A D η)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I) (Fin.castSucc_injective _).injOn
  have hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I).image Fin.castSuccOrderEmb.toOrderHom = I := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I).image Fin.castSucc = I
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withoutLast, Finset.erase_eq_of_notMem hl]
  simpa only [hi] using h

end SerrePositivity.EInfinity.Modules
