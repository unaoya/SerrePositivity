module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellFourthRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathSourceMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingBaseChange

/-!
概要：元の Γ 源から、classifying 比較と二因子分解比較の両方の源へ写す。
方針：既存の非正次数射影を前合成し、各比較の元の P への射影を計算する。
規約：新しい共通源を選ばない。使われ方：右三角形の経路を同じ細分上へ移す。
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
  (d : PostnikovCommonLayerInverse R f c)

def postnikovCommonRightToClassifying : postnikovCommonClassStandardGlueSource R f c d ⟶
    cellResolution R (postnikovCommonRightCellSource R f c d) :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
    cellPathNonpositiveToCell R (postnikovCommonRightCellSource R f c d)

lemma postnikovCommonRightToClassifying_projection :
    postnikovCommonRightToClassifying R f c d ≫
      postnikovCommonRightClassifyingProjection R f c d =
        postnikovCommonClassStandardGlueProjection R f c d := by
  simp only [postnikovCommonRightToClassifying, postnikovCommonRightClassifyingProjection,
    postnikovCommonClassStandardGlueProjection, postnikovCommonRightZeroGlueProjection,
    Category.assoc, reassoc_of% cellPathNonpositiveToCell_projection]

def postnikovCommonRightToFactorization : postnikovCommonClassStandardGlueSource R f c d ⟶
    cellResolution R (cellResolution R (cellResolution R
      (cellResolution R (postnikovCommonClassBase R f c d)))) :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
    cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      cellFixedNonpositiveToFourthCell R (postnikovCommonClassBase R f c d)

lemma postnikovCommonRightToFactorization_projection :
    postnikovCommonRightToFactorization R f c d ≫
      postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d) =
        postnikovCommonClassStandardGlueProjection R f c d := by
  simp only [postnikovCommonRightToFactorization, postnikovCommonClassStandardGlueProjection,
    postnikovCommonRightZeroGlueProjection, postnikovCommonRightCellProjection,
    Category.assoc, cellFixedNonpositiveToFourthCell_projection]

lemma postnikovCommonRightToClassifying_quasiIso :
    QuasiIso (postnikovCommonRightToClassifying R f c d).hom := by
  have := postnikovCommonRightClassifyingProjection_quasiIso R f c d
  have : QuasiIso ((postnikovCommonRightToClassifying R f c d).hom ≫
      (postnikovCommonRightClassifyingProjection R f c d).hom) := by
    change QuasiIso ((postnikovCommonRightToClassifying R f c d ≫
      postnikovCommonRightClassifyingProjection R f c d).hom)
    rw [postnikovCommonRightToClassifying_projection]
    exact postnikovCommonClassStandardGlueProjection_quasiIso R f c d
  exact quasiIso_of_comp_right (postnikovCommonRightToClassifying R f c d).hom
    (postnikovCommonRightClassifyingProjection R f c d).hom

lemma postnikovCommonRightToFactorization_quasiIso :
    QuasiIso (postnikovCommonRightToFactorization R f c d).hom := by
  have := postnikovCellFactorizationProjection_quasiIso R (postnikovCommonClassBase R f c d)
  have : QuasiIso ((postnikovCommonRightToFactorization R f c d).hom ≫
      (postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d)).hom) := by
    change QuasiIso ((postnikovCommonRightToFactorization R f c d ≫
      postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d)).hom)
    rw [postnikovCommonRightToFactorization_projection]
    exact postnikovCommonClassStandardGlueProjection_quasiIso R f c d
  exact quasiIso_of_comp_right (postnikovCommonRightToFactorization R f c d).hom
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d)).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
