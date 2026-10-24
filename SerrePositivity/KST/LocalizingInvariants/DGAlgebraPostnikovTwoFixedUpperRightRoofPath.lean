module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightRoofPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofPrecomposePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugationPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoof

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedUpperRightRoofPath

/-!
概要：fixed class roof の実右三角形を、元の二切断代数と非正次数 roof へ戻す。
方針：源の準同型逆・元の上下段比較・cell 経路反映・connective cover を順に使う。
規約：値の三角形や H⁻² の三角形で代用しない。使われ方：NonpositiveInverseRoof の右経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

set_option quotPrecheck false
local notation "a" => postnikovHomotopyPullbackComparison R (A.obj j).obj 1 (by omega)
local notation "b" => postnikovHomotopyPullbackComparison R
  (B.obj d.layerInverse.zero.stage).obj 1 (by omega)
local notation "c" => postnikovHomotopyPullbackComparison R (B.obj j).obj 1 (by omega)
local notation "ha" => postnikovHomotopyPullbackComparison_quasiIso R (A.obj j).obj 1 (by omega)
local notation "hc" => postnikovHomotopyPullbackComparison_quasiIso R (B.obj j).obj 1 (by omega)
local notation "f₂" => postnikovMap R (f.app j).hom 2
local notation "fₘ" => postnikovClassModelMap R 1 (by omega) (f.app j).hom
local notation "t" => postnikovCommonRightDenDirectMap R f
  d.baseInverse d.layerInverse d.target_le
local notation "t₂" => postnikovMap R t 2
local notation "tₘ" => postnikovClassModelMap R 1 (by omega) t

abbrev rightSourceClassRoof :=
  PostnikovSuccessorClassInverseData.rightSourceClassRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightSourceClassRoofPath : Path.Witness R
    ((d.rightSourceClassRoof R).numerator ≫ fₘ)
    ((d.rightSourceClassRoof R).denominator ≫ tₘ) :=
  PostnikovSuccessorClassInverseData.rightSourceClassRoofPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev upperFixedRightRawRoof :=
  PostnikovSuccessorClassInverseData.upperFixedRightRawRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def upperFixedRightAfterComparison :=
  PostnikovSuccessorClassInverseData.upperFixedRightAfterComparison
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev upperFixedRightRoof :=
  PostnikovSuccessorClassInverseData.upperFixedRightRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def upperFixedRightRoofPath : Path.Witness R
    ((d.upperFixedRightRoof R).numerator ≫ f₂)
    ((d.upperFixedRightRoof R).denominator ≫ t₂) :=
  PostnikovSuccessorClassInverseData.upperFixedRightRoofPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev nonpositiveFixedRightRoof :=
  PostnikovSuccessorClassInverseData.nonpositiveFixedRightRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma nonpositiveFixedRightRoof_nonpositive : (d.nonpositiveFixedRightRoof R).apex.X.IsStrictlyLE 0 :=
  PostnikovSuccessorClassInverseData.nonpositiveFixedRightRoof_nonpositive
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def nonpositiveFixedRightRoofPath : Path.Witness R
    ((d.nonpositiveFixedRightRoof R).numerator ≫ f₂)
    ((d.nonpositiveFixedRightRoof R).denominator ≫ t₂) :=
  PostnikovSuccessorClassInverseData.nonpositiveFixedRightRoofPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
