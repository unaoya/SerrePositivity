module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassLayerIsos
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayerHomology

/-!
概要：次段切断候補の底変更後の両係数を、元の代数の H⁻⁽ⁿ⁺¹⁾ に同定する。
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def sourceCoefficientHomologyIso :
    (d.denominatorLayer R).X.homology (-(n + 1) - 1) ≅
      (B.obj d.layerInverse.zero.stage).obj.X.homology (-(n + 1)) := by
  dsimp only [denominatorLayer, PostnikovCommonCore.roofShiftedDenominatorLayer,
    PostnikovCommonCore.shiftedDenominatorLayer, bimoduleRestrict]
  exact postnikovShiftedLayerHomologyIso R (B.obj d.layerInverse.zero.stage).obj n hn 1

def targetCoefficientHomologyIso :
    (d.numeratorLayer R).X.homology (-(n + 1) - 1) ≅ (A.obj j).obj.X.homology (-(n + 1)) := by
  dsimp only [numeratorLayer, PostnikovCommonCore.postnikovCommonClassTransitionLayer, bimoduleRestrict]
  exact postnikovShiftedLayerHomologyIso R (A.obj j).obj n hn 1

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
