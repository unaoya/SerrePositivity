module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaBImagePath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationImageInverse

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaBImageMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：二 ImageWitness 表示から零底への射の、元の P と零 class 標的への二射影を計算する。
方針：底射等式の同型の逆と、元の零底係数同型の厳密な可換式を合成する。
規約：全経路に適用可能な射の等式。使われ方：元の T 経路との一意性による照合。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightViaBImageToZero_projection :
    postnikovCommonRightViaBImageToZero R f c d hj ≫
      SquareZero.projection (postnikovCommonClassBase R f c d)
        (postnikovCommonRightClassifyingLayer R f c d hj) =
    SquareZero.projection (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (f.app i).hom 1) ≫ postnikovMap R (B.transition hj).hom 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)) :=
  PostnikovCommonCore.postnikovCommonRightViaBImageToZero_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightViaBImageToZero_map :
    postnikovCommonRightViaBImageToZero R f c d hj ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    SquareZero.baseChangeMap
      (((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (f.app i).hom 1) ≫ postnikovMap R (B.transition hj).hom 1)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
        postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 :=
  PostnikovCommonCore.postnikovCommonRightViaBImageToZero_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
