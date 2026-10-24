module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRelativeModels
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoof

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassTransportIso

/-!
概要：元の二切断 class 経路は、係数像模型と標準模型の実相対代数同型を与える。
方針：構成済みの同じ相対経路を transportIso に渡し、元の絶対模型の準同型 span へ戻す。
規約：追加の class 経路を入力しない。使われ方：候補 roof の実三角形の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def classRelativeTransportIso : d.imageRelativeModel R ≅ d.targetRelativeModel R :=
  PostnikovSuccessorClassInverseData.classRelativeTransportIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classRelativeTransportIso_left : (d.classRelativeTransportIso R).hom ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.imageClass R) :=
  PostnikovSuccessorClassInverseData.classRelativeTransportIso_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classRelativeTransportIso_right : (d.classRelativeTransportIso R).hom ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.imageClass R) :=
  PostnikovSuccessorClassInverseData.classRelativeTransportIso_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def classRelativePathRoof : SurjectiveRoof R (d.imageModel R) (d.targetModel R) :=
  PostnikovSuccessorClassInverseData.classRelativePathRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classRelativePathRoof_numerator_quasiIso :
    QuasiIso (d.classRelativePathRoof R).numerator.hom :=
  PostnikovSuccessorClassInverseData.classRelativePathRoof_numerator_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
