module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerFromZero

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreZeroLayerAtCutoff

/-!
概要：共通核の任意の切断次数で、零底の実係数射を元の roof 底へ移す。
方針：元の両脚の零降下に一般の層制限比較を適用する。
規約：同じ underlying 射を保持。使われ方：Common の n=1 特殊化と高次 class の係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)

local instance fromZero_apex_nonpositive : c.roof.apex.X.IsStrictlyLE 0 := c.roof_nonpositive

abbrev zeroDenominatorLayer :=
  zeroDenominatorLayerAt R hn n f c

abbrev zeroNumeratorLayer :=
  zeroNumeratorLayerAt R hn n f c

variable (u : zeroDenominatorLayer R hn f c ⟶ zeroNumeratorLayer R hn f c)

abbrev coefficientFromZero : denominatorLayer R hn f c ⟶ numeratorLayer R hn f c :=
  postnikovLayerFromZero R (B.obj m).obj (A.obj i).obj c.roof.apex n hn
    c.roof.denominator c.roof.numerator u

lemma coefficientFromZero_hom : (coefficientFromZero R hn f c u).hom = u.hom :=
  postnikovLayerFromZero_hom R (B.obj m).obj (A.obj i).obj c.roof.apex n hn
    c.roof.denominator c.roof.numerator u

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
