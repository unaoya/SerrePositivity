module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroDescNaturality
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionBaseEquality

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightBaseIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：共通底の右係数標的を、元の分子と f の合成に沿う標準の層制限と同定する。
方針：零降下の自然性と元の右底三角形で二重制限の底射を厳密に一致させる。
規約：underlying は元の B の層の恒等。使われ方：元の class 自然性との接続。
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
  (d : PostnikovCommonLayerInverse R f c)

local instance commonRightBase_apex_nonpositive :
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex.X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive
local instance commonRightBase_target_lowerBound :
    (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightBase : (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex ⟶
    postnikov R (B.obj i).obj 1 :=
  PostnikovCommonCore.postnikovCommonRightBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightBase_zero :
    postnikovDesc R 0 (postnikovCommonRightBase R f c d ≫
      postnikovTransition R (B.obj i).obj 1 0 (by omega)) =
    postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c d.zero.source_le) ≫
      postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 0 :=
  PostnikovCommonCore.postnikovCommonRightBase_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightBaseIso :
    bimoduleRestrict (postnikovCommonRightBase R f c d)
      (postnikovLayerBaseBimodule R (B.obj i).obj 1 (by omega)) ≅
        postnikovCommonRightLayer R f c d :=
  PostnikovCommonCore.postnikovCommonRightBaseIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightBaseIso_hom : (postnikovCommonRightBaseIso R f c d).hom.hom =
    𝟙 (postnikovLayer R (B.obj i).obj 1) :=
  PostnikovCommonCore.postnikovCommonRightBaseIso_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
