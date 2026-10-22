module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeCoefficientMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMap

/-!
概要：係数模型射は、元の絶対模型の係数射と相対比較を介して厳密に可換となる。
方針：元の二脚と Path.map で後合成した全経路を同時に比較する。
規約：準同型や次数全射性は入力しない。使われ方：元の二切断候補への Γ の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A}
  (m : M ⟶ N) (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N)
  (h : a ≫ SquareZero.coefficientMap A m = b)

def coefficientAbsoluteMap : model M a ⟶ model N b :=
  DGAlgebra.HomotopyPullbackModel.map R a (SquareZero.zeroSection A M)
    b (SquareZero.zeroSection A N) (𝟙 W) (SquareZero.coefficientMap A m) (𝟙 A)
    ((Category.id_comp _).trans h.symm)
    ((Category.id_comp _).trans (SquareZero.zeroSection_coefficientMap m).symm)

lemma coefficientModelMap_comparison : coefficientModelMap m a b h ≫ relativeComparison N b =
    relativeComparison M a ≫ coefficientAbsoluteMap m a b h := by
  apply DGAlgebra.HomotopyPullbackModel.hom_ext R b (SquareZero.zeroSection A N)
  · rw [Category.assoc, relativeComparison_left, coefficientModelMap_left,
      Category.assoc, coefficientAbsoluteMap, DGAlgebra.HomotopyPullbackModel.map_left,
      ← Category.assoc, relativeComparison_left, Category.comp_id]
  · rw [Category.assoc, relativeComparison_right, coefficientModelMap_right,
      Category.assoc, coefficientAbsoluteMap, DGAlgebra.HomotopyPullbackModel.map_right,
      ← Category.assoc, relativeComparison_right, Category.comp_id]
  · rw [Category.assoc, relativeComparison_path, coefficientModelMap_path,
      Category.assoc, coefficientAbsoluteMap, DGAlgebra.HomotopyPullbackModel.map_path,
      ← Category.assoc, relativeComparison_path]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
