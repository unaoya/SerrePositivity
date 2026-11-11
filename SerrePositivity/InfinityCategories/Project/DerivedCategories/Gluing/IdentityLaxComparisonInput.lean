module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityInputConeComparison
/-!
概要：恒等 Hom gluing・指定対角・同じ実 cone 差を持つ固定入力の全比較を公開する。
方針：構成済み中央同値・差終域同値・二つの全関手同型を指定消費型へ代入する。
規約：追加の存在仮定なし。使われ方：K-S• の恒等二脚供給入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

def dgGluingIdentityLaxComparisonInput : DGOdotMilnorIdentityLaxComparisonInput R d where
  gluing := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputLaxEquivalence R d
  difference := dgOdotMilnorIdentityDifferenceValueEquivalence R d
  diagonal := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputDiagonalIso R d
  cone := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputConeIso R d

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
