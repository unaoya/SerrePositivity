module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingContour
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeDoublePath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の classifying 二重経路を、指定した同じ共通底 P 上へ持ち上げる。
方針：零底射の実因子化と二重経路 pullback の持ち上げを使う。
規約：底と class の全二重経路を保持。使われ方：元の Γ 模型での輪郭比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightClassifyingBase :
    postnikovCommonClassBase R f c d ⟶ postnikov R (B.obj j).obj 0 :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightClassifyingProjection :
    cellResolution R (postnikovCommonRightCellSource R f c d) ⟶ postnikovCommonClassBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightClassifyingProjection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightClassifyingProjection_quasiIso :
    QuasiIso (postnikovCommonRightClassifyingProjection R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightClassifyingProjection_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightClassifyingProjection_surjective (n : ℤ) :
    Function.Surjective ((postnikovCommonRightClassifyingProjection R f c d).hom.f n) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingProjection_surjective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (degree := n)

lemma postnikovCommonRightClassifyingProjection_factor :
    postnikovCommonRightClassifyingProjection R f c d ≫
      postnikovCommonRightClassifyingBase R f c d hj =
        postnikovCommonRightClassifyingZeroProjection R f c d hj :=
  PostnikovCommonCore.postnikovCommonRightClassifyingProjection_factor
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingBaseChange_condition :
    ((postnikovCommonRightClassifyingProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d)) ≫
        Path.diagonal R (Path.algebra R (postnikovCommonClassBase R f c d))) ≫
          Path.map R (Path.map R (postnikovCommonRightClassifyingBase R f c d hj)) =
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.map R (Path.map R (SquareZero.projection _ _)) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBaseChange_condition
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightClassifyingBaseChangeHom :
    cellResolution R (postnikovCommonRightCellSource R f c d) ⟶ Path.algebra R
      (Path.algebra R (SquareZero.algebra (postnikovCommonClassBase R f c d)
        (bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)))) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBaseChangeHom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingBaseChangeHom_projection :
    postnikovCommonRightClassifyingBaseChangeHom R f c d hj ≫
      Path.map R (Path.map R (SquareZero.projection _ _)) =
    (postnikovCommonRightClassifyingProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d)) ≫
        Path.diagonal R (Path.algebra R (postnikovCommonClassBase R f c d)) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBaseChangeHom_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingBaseChangeHom_map :
    postnikovCommonRightClassifyingBaseChangeHom R f c d hj ≫
      Path.map R (Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBaseChangeHom_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
