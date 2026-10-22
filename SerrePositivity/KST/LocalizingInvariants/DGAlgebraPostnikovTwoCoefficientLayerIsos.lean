module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassLayerIsos
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayerHomology

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
      (B.obj d.layerInverse.zero.stage).obj.X.homology (-2) := by
  dsimp only [denominatorLayer, postnikovOneRoofShiftedDenominatorLayer, bimoduleRestrict]
  exact postnikovShiftedLayerHomologyIso R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1

def targetCoefficientHomologyIso :
    (d.numeratorLayer R).X.homology (-3) ≅ (A.obj j).obj.X.homology (-2) := by
  dsimp only [numeratorLayer, postnikovCommonClassTransitionLayer, bimoduleRestrict]
  exact postnikovShiftedLayerHomologyIso R (A.obj j).obj 1 (by omega) 1

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
