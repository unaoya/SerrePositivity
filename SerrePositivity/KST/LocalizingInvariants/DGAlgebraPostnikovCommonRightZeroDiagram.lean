module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroDiagram
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：二つの標準 class 標的から共通零標的への元の実射の可換式を証明する。
方針：恒等係数の同型と元の二つの底合成式を、対角直和の両射影で照合する。
規約：元の cell class と底変更を保持。使われ方：橋渡し経路の両端の正規化。
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

lemma postnikovCommonRightClassIso_matrix : (postnikovCommonRightClassIso R f c d).hom.hom =
    biprod.map (𝟙 (postnikovCommonClassBase R f c d).X)
      (𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧)) :=
  PostnikovCommonCore.postnikovCommonRightClassIso_matrix
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightDenClassIso_matrix : (postnikovCommonRightDenClassIso R f c d).hom.hom =
    biprod.map (𝟙 (postnikovCommonClassBase R f c d).X)
      (𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧)) :=
  PostnikovCommonCore.postnikovCommonRightDenClassIso_matrix
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightClassIso_zero : (postnikovCommonRightClassIso R f c d).hom ≫
    postnikovCommonRightClassToZero R f c d =
      SquareZero.baseChangeMap (postnikovCommonRightBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 :=
  PostnikovCommonCore.postnikovCommonRightClassIso_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightDenClassIso_zero : (postnikovCommonRightDenClassIso R f c d).hom ≫
    postnikovCommonRightClassToZero R f c d =
      SquareZero.baseChangeMap (postnikovCommonRightDenBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 :=
  PostnikovCommonCore.postnikovCommonRightDenClassIso_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightStandardClass_zero : postnikovCommonRightStandardClass R f c d ≫
    postnikovCommonRightClassToZero R f c d =
    (cellResolutionMap R (postnikovCommonRightBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega)) ≫
        postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 :=
  PostnikovCommonCore.postnikovCommonRightStandardClass_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightDenStandardClass_zero : postnikovCommonRightDenStandardClass R f c d ≫
    postnikovCommonRightClassToZero R f c d =
    (cellResolutionMap R (postnikovCommonRightDenBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega)) ≫
        postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1 :=
  PostnikovCommonCore.postnikovCommonRightDenStandardClass_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
