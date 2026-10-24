module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightRestoreZero
public import
  SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceNativeModelHomotopy

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightWSource

/-!
概要：元の右像の相対模型上へ W と動く底を前合成し、両端の元の底射を回収する。
方針：relativeLeft と Γ の射影式を使い、relativeRight との厳密な整合を保つ。
規約：W の底を一定に置き換えない。使われ方：movingSourceNativeModelHomotopy の実入力。
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

local notation "α" => SquareZeroExtension.relativeLeft
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "β" => SquareZeroExtension.relativeRight
  (d.rightClassifyingLayer R) (d.rightImageClass R)
def rightWSourcePath : Path.Witness R (α ≫ ((postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫ Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega))))
    (α ≫ d.fixedRightCompletedNativeSource R) :=
  PostnikovSuccessorClassInverseData.rightWSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightWBasePath :=
  PostnikovSuccessorClassInverseData.rightWBasePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWSourcePath_projection : (d.rightWSourcePath R).hom ≫ Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    d.rightWBasePath R :=
  PostnikovSuccessorClassInverseData.rightWSourcePath_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWBasePath_source : d.rightWBasePath R ≫ Path.source R (postnikov R (B.obj j).obj 1) =
    β ≫ postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.rightWBasePath_source
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWBasePath_target : d.rightWBasePath R ≫ Path.target R (postnikov R (B.obj j).obj 1) =
    β ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.rightWBasePath_target
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWBasePath_zero : d.rightWBasePath R ≫
    Path.map R (postnikovTransition R (B.obj j).obj 1 0 (by omega)) =
    (β ≫ postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le) ≫
      Path.diagonal R (postnikov R (B.obj j).obj 0) :=
  PostnikovSuccessorClassInverseData.rightWBasePath_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWClass_projection : ((d.rightWSourcePath R).hom ≫ Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
    Path.map R (SquareZero.projection _ _) = d.rightWBasePath R :=
  PostnikovSuccessorClassInverseData.rightWClass_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
