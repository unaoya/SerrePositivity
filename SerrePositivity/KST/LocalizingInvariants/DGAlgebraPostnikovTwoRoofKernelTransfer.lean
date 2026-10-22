module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofTransfer
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangedKernelHomologyNaturality

/-!
概要：共通底に移した元の二切断射の実 kernel 射を、元の π₂ 射に同定する。
方針：同じ左三角形と元の隣接遷移を、底変更した kernel の自然性へ渡す。
規約：元の H⁻² 射を指定した同型で回収する。使われ方：係数の eventual 逆との接続。
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

def postnikovTwoRoofTransferKernel : kernel (postnikovTwoRoofSourceBase R f c).hom ⟶
    kernel (postnikovTwoRoofDenominatorBase R f c).hom :=
  postnikovBaseChangedKernelMap R (f.app m).hom 1 c.sourceProjection c.roof.denominator
    c.sourceLift (postnikovTwoRoofTransfer_base_square R f c)

lemma postnikovTwoRoofTransferKernel_inclusion :
    postnikovTwoRoofTransferKernel R f c ≫ kernel.ι (postnikovTwoRoofDenominatorBase R f c).hom =
      kernel.ι (postnikovTwoRoofSourceBase R f c).hom ≫ (postnikovTwoRoofTransfer R f c).hom :=
  postnikovBaseChangedKernelMap_inclusion R _ _ _ _ _ _

def postnikovTwoRoofSourceKernelHomologyIso :
    (kernel (postnikovTwoRoofSourceBase R f c).hom).homology (-2) ≅
      (A.obj m).obj.X.homology (-2) :=
  postnikovBaseChangedKernelHomologyIso R (A.obj m).obj 1 c.sourceProjection

lemma postnikovTwoRoofTransferKernel_original :
    homologyMap (postnikovTwoRoofTransferKernel R f c) (-2) ≫
      (postnikovTwoRoofDenominatorKernelHomologyIso R f c).hom =
        (postnikovTwoRoofSourceKernelHomologyIso R f c).hom ≫
          homologyMap (f.app m).hom.hom (-2) :=
  postnikovBaseChangedKernelHomologyIso_naturality R (f.app m).hom 1 c.sourceProjection
    c.roof.denominator c.sourceLift (postnikovTwoRoofTransfer_base_square R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
