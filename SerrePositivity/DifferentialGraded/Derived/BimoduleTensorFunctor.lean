module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorMaps
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # 右相対K-flat因子に関する導来合成関手の関手性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 元の全dg自然な閉零bimodule圏の右相対K-flat対象の充満部分圏。 -/
abbrev RightKFlatBimoduleCategory := ObjectProperty.FullSubcategory
  (fun Q : BimoduleCategory A C E =>
    Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))

/-- 前の変数は局所化済み、後の変数は右相対K-flatな実際のbimoduleとしての関手性。 -/
def derivedComposeWithFunctor : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) where
  obj Q := derivedComposeWith A B C E Q.obj Q.property
  map {Q Q'} g := derivedComposeWithMap A B C E Q.property Q'.property g.hom
  map_id Q := derivedComposeWithMap_id A B C E Q.obj Q.property
  map_comp {Q Q' Q''} g h :=
    derivedComposeWithMap_comp A B C E Q.property Q'.property Q''.property g.hom h.hom

end SerrePositivity.DifferentialGraded.BimoduleTensor
