module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedMappedSource
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGammaSource
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の W source の実経路を、標準 class を貼り合わせた Γ 上へ移す。
方針：既存の二つの非正次数射影を前合成し、全 class 経路と底経路を回収する。
規約：動く一切断底を定数と扱わない。使われ方：native 模型の動く source 比較。
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

def postnikovCommonRightGammaToSource : postnikovCommonClassStandardGlueSource R f c d ⟶
    postnikovCommonRightCellSource R f c d :=
  PostnikovCommonCore.postnikovCommonRightGammaToSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightGammaToSource_projection :
    postnikovCommonRightGammaToSource R f c d ≫ postnikovCommonRightCellProjection R f c d =
      postnikovCommonClassStandardGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonRightGammaToSource_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

variable {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightGammaSourceWitness :=
  PostnikovCommonCore.postnikovCommonRightGammaSourceWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGammaBasePath :=
  PostnikovCommonCore.postnikovCommonRightGammaBasePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGammaSourceWitness_class :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) =
    postnikovCommonRightGammaToSource R f c d ≫
      (postnikovCommonRightFixedMappedClassWitness R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_class
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGammaSourceWitness_projection :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
        (postnikovCommonRightGammaBasePath R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGammaBasePath_zero :
    (postnikovCommonRightGammaBasePath R f c d hj).hom ≫
      Path.map R (postnikovTransition R (B.obj j).obj 1 0 (by omega)) =
    ((postnikovCommonRightGammaBasePath R f c d hj).hom ≫
      Path.source R (postnikov R (B.obj j).obj 1) ≫
        postnikovTransition R (B.obj j).obj 1 0 (by omega)) ≫
          Path.diagonal R (postnikov R (B.obj j).obj 0) :=
  PostnikovCommonCore.postnikovCommonRightGammaBasePath_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
