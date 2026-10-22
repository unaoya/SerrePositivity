module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaAImagePath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationImageInverse

/-!
概要：二 ImageWitness 表示から零底への射の、元の P と零 class 標的への二射影を計算する。
方針：底射等式の同型の逆と、元の零底係数同型の厳密な可換式を合成する。
規約：全経路に適用可能な射の等式。使われ方：native 標準経路 経路との一意性による照合。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightViaAImageToZero_projection :
    postnikovCommonRightViaAImageToZero R f c d hj ≫
      SquareZero.projection (postnikovCommonClassBase R f c d)
        (postnikovCommonRightClassifyingLayer R f c d hj) =
    SquareZero.projection (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (A.transition hj).hom 1) ≫ postnikovMap R (f.app j).hom 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (postnikovCommonRightViaAImageIso R f c d hj).inv ≫ t)
      (postnikovCommonRightCompositeZeroIso_projection R f c d hj)).trans
      (postnikovCellFactorizationImageIso_inv_projection R (A.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
        (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj
        (A.transition hj).hom (f.app j).hom
        rfl))

lemma postnikovCommonRightViaAImageToZero_map :
    postnikovCommonRightViaAImageToZero R f c d hj ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    SquareZero.baseChangeMap
      (((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (A.transition hj).hom 1) ≫ postnikovMap R (f.app j).hom 1)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
        postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (postnikovCommonRightViaAImageIso R f c d hj).inv ≫ t)
      (postnikovCommonRightCompositeZeroIso_map R f c d hj)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1)
          (postnikovCellFactorizationImageIso_inv_map R (A.obj i).obj (B.obj j).obj
            (postnikovCommonClassBase R f c d) 1 (by omega)
            (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
            (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj
            (A.transition hj).hom (f.app j).hom
            rfl))))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
