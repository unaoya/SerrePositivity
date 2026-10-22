module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerFromZero
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonZeroCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofCoefficientBimodules

/-!
概要：任意の roof の共通零底の実係数射を、元の roof 上の実層双加群射へ移す。
方針：底変更層の一般的な零制限比較を適用する。
規約：同じ underlying 射を保持。使われ方：元の底上の係数逆とその cochain 三角形。
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
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (u : postnikovCommonZeroDenominatorLayer R 1 f c ⟶ postnikovCommonZeroNumeratorLayer R 1 f c)

local instance coefficientFromZero_apex_nonpositive : c.roof.apex.X.IsStrictlyLE 0 :=
  c.roof_nonpositive

def postnikovCoefficientFromZero : postnikovOneRoofDenominatorLayer R f c ⟶
    postnikovOneRoofNumeratorLayer R f c :=
  postnikovLayerFromZero R (B.obj m).obj (A.obj i).obj c.roof.apex 1 (by omega)
    c.roof.denominator c.roof.numerator u

lemma postnikovCoefficientFromZero_hom : (postnikovCoefficientFromZero R f c u).hom = u.hom :=
  postnikovLayerFromZero_hom R (B.obj m).obj (A.obj i).obj c.roof.apex 1 (by omega)
    c.roof.denominator c.roof.numerator u

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
