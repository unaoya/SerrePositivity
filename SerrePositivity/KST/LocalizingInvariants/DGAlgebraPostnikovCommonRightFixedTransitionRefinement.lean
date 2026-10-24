module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedGlueZeroMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRight

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedTransitionRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fixed Γ の native 遷移経路の右像を、元の G の同じ Γ 源上の全経路へ同定する。
方針：元の零底射影と fixed 遷移の厳密な右三角形を、同じ前合成射で写す。
規約：元の fixed Γ と元の G を保持。使われ方：class 互換性と実自然性比較の接続。
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

lemma postnikovCommonRightGlueRefined_fixed_map :
    (postnikovCommonRightGlueRefinedPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
      (postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫ Path.map R
        (postnikovCommonRightClassToZero R f c d ≫
          postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightGlueRefined_fixed_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

variable (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedTransitionZeroRightPath :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionZeroRightPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedTransitionZeroRight_hom :
    (postnikovCommonClassFixedTransitionZeroRightPath R f c d hj e).hom =
    (postnikovCommonRightGlueRefinedPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionZeroRight_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
