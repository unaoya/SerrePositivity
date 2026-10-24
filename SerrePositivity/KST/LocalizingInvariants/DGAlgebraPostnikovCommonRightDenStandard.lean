module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenBaseIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClass
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenStandard
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：共通底の右 class 標的を標準の制限層の平方零代数と実同型で比較する。
方針：恒等 underlying 層同型を shift し、元の B の class を元の分母側の指定底で引き戻す。
規約：元の class を結ぶ経路は未主張。使われ方：class の像の比較の基準射。
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

def postnikovCommonRightShiftedDenBaseIso (s : ℤ) :
    bimoduleRestrict (postnikovCommonRightDenBase R f c d)
      (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) s) ≅
        DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) s :=
  PostnikovCommonCore.postnikovCommonRightShiftedDenBaseIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

lemma postnikovCommonRightShiftedDenBaseIso_hom (s : ℤ) :
    (postnikovCommonRightShiftedDenBaseIso R f c d s).hom.hom =
      𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦s⟧) :=
  PostnikovCommonCore.postnikovCommonRightShiftedDenBaseIso_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

def postnikovCommonRightDenClassIso :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (postnikovCommonRightDenBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1)) ≅
          postnikovCommonRightClassTarget R f c d :=
  PostnikovCommonCore.postnikovCommonRightDenClassIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightDenClassIso_projection : (postnikovCommonRightDenClassIso R f c d).hom ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  PostnikovCommonCore.postnikovCommonRightDenClassIso_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightDenStandardClass : cellResolution R (postnikovCommonClassBase R f c d) ⟶
    postnikovCommonRightClassTarget R f c d :=
  PostnikovCommonCore.postnikovCommonRightDenStandardClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightDenStandardClass_projection :
    postnikovCommonRightDenStandardClass R f c d ≫
    SquareZero.projection _ _ = cellAugmentation R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightDenStandardClass_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
