module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofCommonKernels
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofRightTraces

/-!
概要：分子・分母側の実 kernel 射を共通 kernel へ移し、元の H⁻² 射を回収する。
方針：共通 kernel のホモロジーを元の Bᵢ に同定し、両端で同じ係数同型を使う。
規約：実代数の逆を仮定しない。使われ方：係数逆の持ち上げの両三角形。
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

def postnikovTwoRoofCommonKernelHomologyIso :
    (postnikovTwoRoofRightCommonKernel R f c).homology (-2) ≅ (B.obj i).obj.X.homology (-2) := by
  have := postnikovTwoRoofRightFirstKernel_quasiIso R f c
  exact (asIso (homologyMap (postnikovTwoRoofRightFirstKernel R f c) (-2))).symm ≪≫
    postnikovBaseChangedKernelHomologyIso R (B.obj i).obj 1 (postnikovTwoRoofRightFirst R f c)

lemma postnikovTwoRoofRightFirstKernel_original :
    homologyMap (postnikovTwoRoofRightFirstKernel R f c) (-2) ≫
      (postnikovTwoRoofCommonKernelHomologyIso R f c).hom =
    (postnikovBaseChangedKernelHomologyIso R (B.obj i).obj 1
      (postnikovTwoRoofRightFirst R f c)).hom := by
  have := postnikovTwoRoofRightFirstKernel_quasiIso R f c
  change homologyMap (postnikovTwoRoofRightFirstKernel R f c) (-2) ≫
    (inv (homologyMap (postnikovTwoRoofRightFirstKernel R f c) (-2)) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _

lemma postnikovTwoRoofRightSecondKernel_original :
    homologyMap (postnikovTwoRoofRightSecondKernel R f c) (-2) ≫
      (postnikovTwoRoofCommonKernelHomologyIso R f c).hom =
    (postnikovBaseChangedKernelHomologyIso R (B.obj i).obj 1
      (postnikovTwoRoofRightSecond R f c)).hom := by
  have := postnikovTwoRoofRightFirstKernel_quasiIso R f c
  have := postnikovTwoRoofRightSecondKernel_quasiIso R f c
  exact moduleIsoSpan_reverse _ _ _ _ (postnikovTwoRoofRightKernelHomologyIso_original R f c)

def postnikovTwoRoofNumeratorCommonKernel :
    kernel (postnikovExtensionBaseChangeBase R (A.obj i).obj 1 c.roof.numerator).hom ⟶
      postnikovTwoRoofRightCommonKernel R f c :=
  postnikovTwoRoofNumeratorKernelMap R f c ≫ postnikovTwoRoofRightFirstKernel R f c

def postnikovTwoRoofDenominatorCommonKernel :
    kernel (postnikovTwoRoofDenominatorBase R f c).hom ⟶
      postnikovTwoRoofRightCommonKernel R f c :=
  postnikovTwoRoofDenominatorKernelMap R f c ≫ postnikovTwoRoofRightSecondKernel R f c

lemma postnikovTwoRoofNumeratorCommonKernel_original :
    homologyMap (postnikovTwoRoofNumeratorCommonKernel R f c) (-2) ≫
      (postnikovTwoRoofCommonKernelHomologyIso R f c).hom =
    (postnikovBaseChangedKernelHomologyIso R (A.obj i).obj 1 c.roof.numerator).hom ≫
      homologyMap (f.app i).hom.hom (-2) := by
  have hc := homologyMap_comp (postnikovTwoRoofNumeratorKernelMap R f c)
    (postnikovTwoRoofRightFirstKernel R f c) (-2)
  exact (congrArg (fun t => t ≫ (postnikovTwoRoofCommonKernelHomologyIso R f c).hom) hc).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => homologyMap (postnikovTwoRoofNumeratorKernelMap R f c) (-2) ≫ t)
        (postnikovTwoRoofRightFirstKernel_original R f c)).trans
          (postnikovTwoRoofNumeratorKernelMap_original R f c)))

lemma postnikovTwoRoofDenominatorCommonKernel_original :
    homologyMap (postnikovTwoRoofDenominatorCommonKernel R f c) (-2) ≫
      (postnikovTwoRoofCommonKernelHomologyIso R f c).hom =
    (postnikovTwoRoofDenominatorKernelHomologyIso R f c).hom ≫
      homologyMap (B.transition hi).hom.hom (-2) := by
  have hc := homologyMap_comp (postnikovTwoRoofDenominatorKernelMap R f c)
    (postnikovTwoRoofRightSecondKernel R f c) (-2)
  exact (congrArg (fun t => t ≫ (postnikovTwoRoofCommonKernelHomologyIso R f c).hom) hc).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => homologyMap (postnikovTwoRoofDenominatorKernelMap R f c) (-2) ≫ t)
        (postnikovTwoRoofRightSecondKernel_original R f c)).trans
          (postnikovTwoRoofDenominatorKernelMap_original R f c)))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
