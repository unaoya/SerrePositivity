module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightBaseIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClass
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightStandardClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：共通底の右 class 標的を標準の制限層の平方零代数と実同型で比較する。
方針：恒等 underlying 層同型を shift し、元の B の class を指定底で引き戻す。
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

def postnikovCommonRightShiftedBaseIso (s : ℤ) :
    bimoduleRestrict (postnikovCommonRightBase R f c d)
      (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) s) ≅
        DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) s :=
  PostnikovCommonCore.postnikovCommonRightShiftedBaseIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

lemma postnikovCommonRightShiftedBaseIso_hom (s : ℤ) :
    (postnikovCommonRightShiftedBaseIso R f c d s).hom.hom =
      𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦s⟧) :=
  PostnikovCommonCore.postnikovCommonRightShiftedBaseIso_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (s := s)

def postnikovCommonRightClassIso :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (postnikovCommonRightBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1)) ≅
          postnikovCommonRightClassTarget R f c d :=
  PostnikovCommonCore.postnikovCommonRightClassIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightClassIso_projection : (postnikovCommonRightClassIso R f c d).hom ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  PostnikovCommonCore.postnikovCommonRightClassIso_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightStandardClass : cellResolution R (postnikovCommonClassBase R f c d) ⟶
    postnikovCommonRightClassTarget R f c d :=
  PostnikovCommonCore.postnikovCommonRightStandardClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightStandardClass_projection : postnikovCommonRightStandardClass R f c d ≫
    SquareZero.projection _ _ = cellAugmentation R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightStandardClass_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
