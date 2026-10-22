module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectZeroMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourSourceRight

/-!
概要：元の Γ 上で、直接 B 遷移と二段合成の実 class 経路を同じ P 係数に揃える。
方針：同じ四重 cell 比較を元の Γ 射で前合成し、零底係数へ厳密に移す。
規約：元の Γ 射影と指定自然性を保持。使われ方：分母の直接遷移の実二重比較。
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

def postnikovCommonRightDenDirectCommonPath :=
  postnikovCellFactorizationDirectCommonWitness R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R f c d hj)

def postnikovCommonRightDenAffineCommonPath :=
  postnikovCellFactorizationAffineCommonWitness R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R f c d hj)

def postnikovCommonRightDenDirectPath :=
  (((postnikovCommonRightDenDirectCommonPath R f c d hj).mapOver (𝟙 _)
    (postnikovCommonRightDenDirectToZero R f c d hj)
    ((postnikovCommonRightDenDirectToZero_projection R f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightToFactorization R f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightToFactorization_projection R f c d)

def postnikovCommonRightDenAffinePath :=
  (((postnikovCommonRightDenAffineCommonPath R f c d hj).mapOver (𝟙 _)
    (postnikovCommonRightDenDirectToZero R f c d hj)
    ((postnikovCommonRightDenDirectToZero_projection R f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightToFactorization R f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightToFactorization_projection R f c d)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
