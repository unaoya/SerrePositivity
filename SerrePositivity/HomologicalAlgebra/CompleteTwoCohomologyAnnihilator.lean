module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # 完備な二次数導来対象の標準Koszul塔からの零化

比較同型を追加の入力にせず、標準再構成と既存の二段零化を合成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

end SerrePositivity
