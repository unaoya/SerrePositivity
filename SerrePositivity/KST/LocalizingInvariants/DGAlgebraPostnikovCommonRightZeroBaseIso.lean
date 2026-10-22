module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

/-!
概要：元の右 class 標的を、共通零標的の元の底への底変更と実同型で比較する。
方針：制限合成の恒等係数同型を shift し、平方零関手で同型と元の射影を保持する。
規約：元の零標的への射を保つ。使われ方：貼り合わせた経路を元の class 標的へ戻す。
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

def postnikovCommonRightZeroShiftIso : DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) 1 ≅
    bimoduleRestrict (postnikovCommonRightZeroBase R f c d)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1) :=
  (DGBimoduleShift.functor (postnikovCommonClassBase R f c d) 1).mapIso
    ((postnikovCommonRightZeroLayerIso R f c d).symm) ≪≫
      DGBimoduleShift.restrictionIso (postnikovCommonRightZeroBase R f c d)
        (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1

def postnikovCommonRightZeroBaseIso : postnikovCommonRightClassTarget R f c d ≅
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (postnikovCommonRightZeroBase R f c d)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)) :=
  SquareZero.coefficientIso _ (postnikovCommonRightZeroShiftIso R f c d)

lemma postnikovCommonRightZeroBaseIso_hom : (postnikovCommonRightZeroBaseIso R f c d).hom =
    SquareZero.coefficientMap _ (postnikovCommonRightZeroCoefficient R f c d) := rfl

lemma postnikovCommonRightZeroBaseIso_projection : (postnikovCommonRightZeroBaseIso R f c d).hom ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.coefficientMap_projection _ _

lemma postnikovCommonRightZeroBaseIso_inv_projection :
    (postnikovCommonRightZeroBaseIso R f c d).inv ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ := SquareZero.coefficientMap_projection _ _

lemma postnikovCommonRightZeroBaseIso_map : (postnikovCommonRightZeroBaseIso R f c d).hom ≫
    SquareZero.baseChangeMap (postnikovCommonRightZeroBase R f c d)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1) =
        postnikovCommonRightClassToZero R f c d :=
  SquareZero.coefficientMap_baseChangeMap _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
