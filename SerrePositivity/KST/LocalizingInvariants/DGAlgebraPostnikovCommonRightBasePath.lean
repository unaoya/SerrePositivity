module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathNonpositive
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathDiscreteTarget

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightBasePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の指定右経路を、非正次数共通源上の二つの標準 cell class の実経路へ移す。
方針：cell 比較への経路反映と実 class の後合成を使い、零底への像を定数経路と照合する。
規約：元の経路を入力とし、共通源の全射準同型性を保持。使われ方：class 比較の貼合せ。
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

local instance commonBasePath_apex_nonpositive :
    (postnikovCommonClassBase R f c d).X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive
local instance commonBasePath_target_lowerBound :
    (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightBasePath : Path.Witness R (postnikovCommonRightBase R f c d)
    (postnikovCommonRightDenBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightBasePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightBasePath_zero : (postnikovCommonRightBasePath R f c d).hom ≫
    Path.map R (postnikovTransition R (B.obj i).obj 1 0 (by omega)) =
    (postnikovCommonRightBase R f c d ≫ postnikovTransition R (B.obj i).obj 1 0 (by omega)) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  PostnikovCommonCore.postnikovCommonRightBasePath_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

abbrev postnikovCommonRightCellSource :=
  PostnikovCommonCore.postnikovCommonRightCellSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightCellProjection : postnikovCommonRightCellSource R f c d ⟶
    postnikovCommonClassBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightCellProjection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightCellProjection_quasiIso :
    QuasiIso (postnikovCommonRightCellProjection R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightCellProjection_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightCellProjection_surjective (n : ℤ) :
    Function.Surjective ((postnikovCommonRightCellProjection R f c d).hom.f n) :=
  PostnikovCommonCore.postnikovCommonRightCellProjection_surjective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (degree := n)

def postnikovCommonRightCellClassWitness : Path.Witness R
    (cellPathNonpositiveComparison R (postnikovCommonRightBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega))
    (cellPathNonpositiveComparison R (postnikovCommonRightDenBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega)) :=
  PostnikovCommonCore.postnikovCommonRightCellClassWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightCellClassWitness_zero :
    (postnikovCommonRightCellClassWitness R f c d).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj i).obj 1)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
          postnikovTransition R (B.obj i).obj 1 0 (by omega)) =
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightBase R f c d ≫
      postnikovTransition R (B.obj i).obj 1 0 (by omega)) ≫
        Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  PostnikovCommonCore.postnikovCommonRightCellClassWitness_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
