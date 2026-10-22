module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofRightKernels
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofRightComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPathKernelHomology

/-!
概要：元の右経路の両端の二切断 kernel を共通 kernel へ準同型で移し、係数を同定。
方針：同じ実経路による kernel 比較を元の一切断逆に適用する。
規約：指定した元の H⁻² 同型を保持。使われ方：π₂ の逆の実代数への持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

attribute [local instance] roof_nonpositive upper_nonpositive

def postnikovTwoRoofRightCommonKernel : Complex R :=
  kernel (postnikovTwoRoofRightCommonBase R f c).hom

def postnikovTwoRoofRightFirstKernel :
    kernel (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
      (postnikovTwoRoofRightFirst R f c)).hom ⟶ postnikovTwoRoofRightCommonKernel R f c :=
  PathBaseChange.firstKernel R _ _

def postnikovTwoRoofRightSecondKernel :
    kernel (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
      (postnikovTwoRoofRightSecond R f c)).hom ⟶ postnikovTwoRoofRightCommonKernel R f c :=
  PathBaseChange.secondKernel R _ _ _ (postnikovTwoRoofRightWitness R f c)

lemma postnikovTwoRoofRightFirstKernel_quasiIso :
    QuasiIso (postnikovTwoRoofRightFirstKernel R f c) :=
  PathBaseChange.firstKernel_quasiIso R _ _

lemma postnikovTwoRoofRightSecondKernel_quasiIso :
    QuasiIso (postnikovTwoRoofRightSecondKernel R f c) :=
  PathBaseChange.secondKernel_quasiIso R _ _ _ _

def postnikovTwoRoofRightKernelHomologyIso :
    (kernel (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
      (postnikovTwoRoofRightFirst R f c)).hom).homology (-2) ≅
    (kernel (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
      (postnikovTwoRoofRightSecond R f c)).hom).homology (-2) :=
  PathBaseChange.kernelHomologyIso R _ _ _ (postnikovTwoRoofRightWitness R f c) (-2)

lemma postnikovTwoRoofRightKernelHomologyIso_original :
    (postnikovTwoRoofRightKernelHomologyIso R f c).hom ≫
      (postnikovBaseChangedKernelHomologyIso R (B.obj i).obj 1
        (postnikovTwoRoofRightSecond R f c)).hom =
    (postnikovBaseChangedKernelHomologyIso R (B.obj i).obj 1
      (postnikovTwoRoofRightFirst R f c)).hom :=
  postnikovPathKernelHomologyIso_original R (B.obj i).obj c.roof.apex 1 _ _
    (postnikovTwoRoofRightWitness R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
