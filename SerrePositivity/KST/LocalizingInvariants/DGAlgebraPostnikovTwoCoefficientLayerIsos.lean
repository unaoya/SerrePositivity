module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassLayerIsos
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayerHomology

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCoefficientLayerIsos

/-!
概要：二切断候補の底変更後の両係数を、元の代数の H⁻² に同定する。
方針：底制限の underlying 複体を明示して、元の shift 層同型を使う。
規約：係数の底作用だけを変更する。使われ方：実模型射と roof の層作用の包装。
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

def sourceCoefficientHomologyIso :
    (d.denominatorLayer R).X.homology (-3) ≅
      (B.obj d.layerInverse.zero.stage).obj.X.homology (-2) :=
  PostnikovSuccessorClassInverseData.sourceCoefficientHomologyIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetCoefficientHomologyIso :
    (d.numeratorLayer R).X.homology (-3) ≅ (A.obj j).obj.X.homology (-2) :=
  PostnikovSuccessorClassInverseData.targetCoefficientHomologyIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
