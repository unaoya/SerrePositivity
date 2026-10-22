module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositivePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveNativeInverseRoof

/-!
概要：正規化した逆の元の右三角形を、非正次数の実経路代数への射として供給する。
方針：元の経路射を cover へ一意に持ち上げ、包含・両端の元の射との式を保つ。
規約：経路の実射を選び直さない。使われ方：非正次数 class cospan の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}
  {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R f i m hi)
  [(Y.obj i).X.IsStrictlyLE 0]

local instance : c.roof.apex.X.IsStrictlyLE 0 := c.roof_nonpositive

def NonpositiveInverseRoof.rightPathLift : c.roof.apex ⟶ NonpositivePath.algebra R (Y.obj i) :=
  NonpositivePath.lift R c.rightPath

lemma NonpositiveInverseRoof.rightPathLift_inclusion :
    c.rightPathLift R ≫ connectiveCoverInclusion R (Path.algebra R (Y.obj i)) =
      c.rightPath.hom := NonpositivePath.lift_inclusion R c.rightPath

lemma NonpositiveInverseRoof.rightPathLift_source :
    c.rightPathLift R ≫ NonpositivePath.source R (Y.obj i) = c.roof.numerator ≫ f.app i :=
  NonpositivePath.lift_source R c.rightPath

lemma NonpositiveInverseRoof.rightPathLift_target :
    c.rightPathLift R ≫ NonpositivePath.target R (Y.obj i) =
      c.roof.denominator ≫ Y.transition hi := NonpositivePath.lift_target R c.rightPath

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
