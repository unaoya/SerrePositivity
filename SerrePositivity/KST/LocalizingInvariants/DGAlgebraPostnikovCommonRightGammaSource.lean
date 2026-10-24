module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedMappedSource
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue

/-!
概要：元の W source の実経路を、標準 class を貼り合わせた Γ 上へ移す。
方針：既存の二つの非正次数射影を前合成し、全 class 経路と底経路を回収する。
規約：動く一切断底を定数と扱わない。使われ方：native 模型の動く source 比較。
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

def postnikovCommonRightGammaToSource : postnikovCommonClassStandardGlueSource R f c d ⟶
    postnikovCommonRightCellSource R f c d :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
    cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d)

lemma postnikovCommonRightGammaToSource_projection :
    postnikovCommonRightGammaToSource R f c d ≫ postnikovCommonRightCellProjection R f c d =
      postnikovCommonClassStandardGlueProjection R f c d := by
  simp only [postnikovCommonRightGammaToSource, postnikovCommonClassStandardGlueProjection,
    postnikovCommonRightZeroGlueProjection, Category.assoc]

variable {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightGammaSourceWitness :=
  (postnikovCommonRightFixedMappedSourceWitness R f c d hj).precomp
    (postnikovCommonRightGammaToSource R f c d)

def postnikovCommonRightGammaBasePath :=
  (((postnikovCommonRightBasePath R f c d).postcomp
    (postnikovMap R (B.transition hj).hom 1)).precomp
      (postnikovCommonClassStandardGlueProjection R f c d))

lemma postnikovCommonRightGammaSourceWitness_class :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) =
    postnikovCommonRightGammaToSource R f c d ≫
      (postnikovCommonRightFixedMappedClassWitness R f c d hj).hom := by
  change (postnikovCommonRightGammaToSource R f c d ≫ _) ≫ _ = _
  rw [Category.assoc, postnikovCommonRightFixedMappedSourceWitness_class]

lemma postnikovCommonRightGammaSourceWitness_projection :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
        (postnikovCommonRightGammaBasePath R f c d hj).hom := by
  change (postnikovCommonRightGammaToSource R f c d ≫ _) ≫ _ = _
  rw [Category.assoc, postnikovCommonRightFixedMappedSourceWitness_projection,
    ← Category.assoc, postnikovCommonRightGammaToSource_projection]
  rfl

lemma postnikovCommonRightGammaBasePath_zero :
    (postnikovCommonRightGammaBasePath R f c d hj).hom ≫
      Path.map R (postnikovTransition R (B.obj j).obj 1 0 (by omega)) =
    ((postnikovCommonRightGammaBasePath R f c d hj).hom ≫
      Path.source R (postnikov R (B.obj j).obj 1) ≫
        postnikovTransition R (B.obj j).obj 1 0 (by omega)) ≫
          Path.diagonal R (postnikov R (B.obj j).obj 0) := by
  have : (postnikov R (B.obj j).obj 0).X.IsStrictlyGE 0 := by
    simpa only [neg_zero] using postnikov_lowerBound R (B.obj j).obj 0
  have h := Path.map_to_discrete_constant R
    ((postnikovCommonRightGammaBasePath R f c d hj).hom ≫
      Path.map R (postnikovTransition R (B.obj j).obj 1 0 (by omega)))
  simpa only [Category.assoc, Path.map_source] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
