module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectData

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenDirectZeroMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：直接 B 遷移の係数表示から、元の P と零 class 標的への二射影を保持する。
方針：二段表示との実同型と、元の分母の零底係数同型の射影式を合成する。
規約：元の全係数射を保持。使われ方：同じ Γ 上の直接・二段自然性の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightDenDirectToZero_projection :
    postnikovCommonRightDenDirectToZero R f c d hj ≫ SquareZero.projection
      (postnikovCommonClassBase R f c d) (postnikovCommonRightClassifyingLayer R f c d hj) =
    SquareZero.projection (postnikovCommonClassBase R f c d)
      (bimoduleRestrict ((postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
        postnikovMap R (postnikovCommonRightDenDirectMap R f c d hj) 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)) :=
  PostnikovCommonCore.postnikovCommonRightDenDirectToZero_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightDenDirectToZero_map :
    postnikovCommonRightDenDirectToZero R f c d hj ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    SquareZero.baseChangeMap
      ((postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
        postnikovMap R (postnikovCommonRightDenDirectMap R f c d hj) 1)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
        postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 :=
  PostnikovCommonCore.postnikovCommonRightDenDirectToZero_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
