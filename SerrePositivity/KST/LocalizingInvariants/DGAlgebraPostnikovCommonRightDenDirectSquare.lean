module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectPaths
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

/-!
概要：元の Γ 上で、直接 B 遷移の単一自然性と二段 affine 合成を実比較する。
方針：同じ四重 cell 二重経路を前合成し、P 上の同じ係数へ移す。
規約：直接経路は元の単一 ImageWitness の全射として同定。使われ方：右分母三角形。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightDenDirectAffineSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenDirectPath R f c d hj)
    (postnikovCommonRightDenAffinePath R f c d hj) := by
  let h := postnikovCellFactorizationDirectAffineCommonSquare R (B.obj d.zero.stage).obj
    (B.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R f c d hj)
  exact ((h.mapOver (𝟙 _) (postnikovCommonRightDenDirectToZero R f c d hj)
    ((postnikovCommonRightDenDirectToZero_projection R f c d hj).trans
      (Category.comp_id _).symm)).precomp (postnikovCommonRightToFactorization R f c d)).rebase
      (q' := postnikovCommonClassStandardGlueProjection R f c d) (by
        rw [Category.comp_id]
        exact postnikovCommonRightToFactorization_projection R f c d)

lemma postnikovCommonRightDenDirectPath_hom :
    (postnikovCommonRightDenDirectPath R f c d hj).hom =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCellImageRelative R (B.obj d.zero.stage).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
        (postnikovCommonRightDenDirectMap R f c d hj)).hom ≫
      Path.map R (postnikovCommonRightDenDirectToZero R f c d hj) := by
  change (postnikovCommonRightToFactorization R f c d ≫
    ((postnikovCommonRightDenDirectCommonPath R f c d hj).hom ≫
      Path.map R (postnikovCommonRightDenDirectToZero R f c d hj))) = _
  let h := postnikovCellFactorizationDirectCommon_image_hom R (B.obj d.zero.stage).obj
    (B.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R f c d hj)
  let k := congrArg (fun t => postnikovCommonRightToFactorization R f c d ≫
    (t ≫ Path.map R (postnikovCommonRightDenDirectToZero R f c d hj))) h
  simpa only [postnikovCommonRightDenDirectCommonPath, postnikovCommonRightImageToSecond,
    Category.assoc] using k

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
