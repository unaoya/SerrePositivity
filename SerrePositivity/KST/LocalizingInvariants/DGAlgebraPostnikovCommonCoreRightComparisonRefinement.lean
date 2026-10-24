module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellFourthRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathSourceMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardZeroGlue
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingBaseChange

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightToClassifying : postnikovCommonClassStandardGlueSource R hn f c d ⟶
    cellResolution R (postnikovCommonRightCellSource R hn f c d) :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
    cellPathNonpositiveToCell R (postnikovCommonRightCellSource R hn f c d)

lemma postnikovCommonRightToClassifying_projection :
    postnikovCommonRightToClassifying R hn f c d ≫
      postnikovCommonRightClassifyingProjection R hn f c d =
        postnikovCommonClassStandardGlueProjection R hn f c d := by
  simp only [postnikovCommonRightToClassifying, postnikovCommonRightClassifyingProjection,
    postnikovCommonClassStandardGlueProjection, postnikovCommonRightZeroGlueProjection,
    Category.assoc, reassoc_of% cellPathNonpositiveToCell_projection]

def postnikovCommonRightToFactorization : postnikovCommonClassStandardGlueSource R hn f c d ⟶
    cellResolution R (cellResolution R (cellResolution R
      (cellResolution R (postnikovCommonClassBase R hn f c d)))) :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
    cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
      cellFixedNonpositiveToFourthCell R (postnikovCommonClassBase R hn f c d)

lemma postnikovCommonRightToFactorization_projection :
    postnikovCommonRightToFactorization R hn f c d ≫
      postnikovCellFactorizationProjection R (postnikovCommonClassBase R hn f c d) =
        postnikovCommonClassStandardGlueProjection R hn f c d := by
  simp only [postnikovCommonRightToFactorization, postnikovCommonClassStandardGlueProjection,
    postnikovCommonRightZeroGlueProjection, postnikovCommonRightCellProjection,
    Category.assoc, cellFixedNonpositiveToFourthCell_projection]

lemma postnikovCommonRightToClassifying_quasiIso :
    QuasiIso (postnikovCommonRightToClassifying R hn f c d).hom := by
  have := postnikovCommonRightClassifyingProjection_quasiIso R hn f c d
  have : QuasiIso ((postnikovCommonRightToClassifying R hn f c d).hom ≫
      (postnikovCommonRightClassifyingProjection R hn f c d).hom) := by
    change QuasiIso ((postnikovCommonRightToClassifying R hn f c d ≫
      postnikovCommonRightClassifyingProjection R hn f c d).hom)
    rw [postnikovCommonRightToClassifying_projection]
    exact postnikovCommonClassStandardGlueProjection_quasiIso R hn f c d
  exact quasiIso_of_comp_right (postnikovCommonRightToClassifying R hn f c d).hom
    (postnikovCommonRightClassifyingProjection R hn f c d).hom

lemma postnikovCommonRightToFactorization_quasiIso :
    QuasiIso (postnikovCommonRightToFactorization R hn f c d).hom := by
  have := postnikovCellFactorizationProjection_quasiIso R (postnikovCommonClassBase R hn f c d)
  have : QuasiIso ((postnikovCommonRightToFactorization R hn f c d).hom ≫
      (postnikovCellFactorizationProjection R (postnikovCommonClassBase R hn f c d)).hom) := by
    change QuasiIso ((postnikovCommonRightToFactorization R hn f c d ≫
      postnikovCellFactorizationProjection R (postnikovCommonClassBase R hn f c d)).hom)
    rw [postnikovCommonRightToFactorization_projection]
    exact postnikovCommonClassStandardGlueProjection_quasiIso R hn f c d
  exact quasiIso_of_comp_right (postnikovCommonRightToFactorization R hn f c d).hom
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R hn f c d)).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
