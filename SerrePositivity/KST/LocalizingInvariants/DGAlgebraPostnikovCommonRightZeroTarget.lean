module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightStandardClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenStandard
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionComposition

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の共通底上の右 class 標的を、B の零底平方零標的へ写す。
方針：元の零底射の合成と制限合成同型を使い、恒等係数の shift を保つ。
規約：分子・分母側の元の底射への合成式を保持。使われ方：class 経路の共通標的。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

local instance rightZero_apex_nonpositive : (postnikovCommonClassBase R f c d).X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive
local instance rightZero_target_lowerBound : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightZeroBase : postnikovCommonClassBase R f c d ⟶
    postnikov R (B.obj i).obj 0 :=
  PostnikovCommonCore.postnikovCommonRightZeroBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroBase_num : postnikovCommonRightZeroBase R f c d =
    postnikovCommonRightBase R f c d ≫ postnikovTransition R (B.obj i).obj 1 0 (by omega) :=
  PostnikovCommonCore.postnikovCommonRightZeroBase_num
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroBase_den : postnikovCommonRightZeroBase R f c d =
    postnikovCommonRightDenBase R f c d ≫ postnikovTransition R (B.obj i).obj 1 0 (by omega) :=
  PostnikovCommonCore.postnikovCommonRightZeroBase_den
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroLayerIso :
    bimoduleRestrict (postnikovCommonRightZeroBase R f c d)
      (postnikovLayerZeroBimodule R (B.obj i).obj 1) ≅ postnikovCommonRightLayer R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroLayerIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroCoefficient :
    DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) 1 ⟶
      bimoduleRestrict (postnikovCommonRightZeroBase R f c d)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1) :=
  PostnikovCommonCore.postnikovCommonRightZeroCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroCoefficient_hom :
    (postnikovCommonRightZeroCoefficient R f c d).hom =
      𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧) :=
  PostnikovCommonCore.postnikovCommonRightZeroCoefficient_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightClassToZero : postnikovCommonRightClassTarget R f c d ⟶
    postnikovZeroClassTarget R (B.obj i).obj 1 1 :=
  PostnikovCommonCore.postnikovCommonRightClassToZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightClassToZero_projection : postnikovCommonRightClassToZero R f c d ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ ≫ postnikovCommonRightZeroBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightClassToZero_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightClassToZero_hom : (postnikovCommonRightClassToZero R f c d).hom =
    biprod.map (postnikovCommonRightZeroBase R f c d).hom
      (𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧)) :=
  PostnikovCommonCore.postnikovCommonRightClassToZero_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
