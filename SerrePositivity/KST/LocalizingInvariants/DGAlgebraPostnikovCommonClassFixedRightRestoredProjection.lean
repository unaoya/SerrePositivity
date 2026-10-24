module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightRestored

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightRestoredProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の P 上へ復元した右 class 二重経路の native 零 class 像と全底射影を同定する。
方針：表示移送の全射保存と、底変更二重経路の厳密な二射影式を合成する。
規約：元の全二重経路を回収する。使われ方：右模型三角形の coherence の比較。
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
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedRightRestoredSquare_hom :
    (postnikovCommonClassFixedRightRestoredSquare R f c d hj e).hom =
      (postnikovCommonClassFixedRightRelativeSquare R f c d hj e).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredSquare_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedRightRestoredSquare_map :
    (postnikovCommonClassFixedRightRestoredSquare R f c d hj e).hom ≫ Path.map R
      (Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (postnikovCommonClassFixedRightZeroSquare R f c d hj e).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredSquare_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedRightRestoredSquare_projection :
    (postnikovCommonClassFixedRightRestoredSquare R f c d hj e).hom ≫ Path.map R
      (Path.map R (SquareZero.projection (postnikovCommonClassBase R f c d)
        (postnikovCommonRightClassifyingLayer R f c d hj))) =
    (postnikovCommonClassStandardGlueProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d)) ≫
        Path.diagonal R (Path.algebra R (postnikovCommonClassBase R f c d)) :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredSquare_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
