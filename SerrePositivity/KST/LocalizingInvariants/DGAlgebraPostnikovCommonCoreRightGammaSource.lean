module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedMappedSource
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardZeroGlue

/-!
概要：元の W source の実経路を、標準 class を貼り合わせた Γ 上へ移す。
方針：既存の二つの非正次数射影を前合成し、全 class 経路と底経路を回収する。
規約：動く下段切断底を定数と扱わない。使われ方：native 模型の動く source 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

def postnikovCommonRightGammaToSource : postnikovCommonClassStandardGlueSource R hn f c d ⟶
    postnikovCommonRightCellSource R hn f c d :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
    cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d)

lemma postnikovCommonRightGammaToSource_projection :
    postnikovCommonRightGammaToSource R hn f c d ≫ postnikovCommonRightCellProjection R hn f c d =
      postnikovCommonClassStandardGlueProjection R hn f c d := by
  simp only [postnikovCommonRightGammaToSource, postnikovCommonClassStandardGlueProjection,
    postnikovCommonRightZeroGlueProjection, Category.assoc]

variable {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightGammaSourceWitness :=
  (postnikovCommonRightFixedMappedSourceWitness R hn f c d hj).precomp
    (postnikovCommonRightGammaToSource R hn f c d)

def postnikovCommonRightGammaBasePath :=
  (((postnikovCommonRightBasePath R hn f c d).postcomp
    (postnikovMap R (B.transition hj).hom n)).precomp
      (postnikovCommonClassStandardGlueProjection R hn f c d))

lemma postnikovCommonRightGammaSourceWitness_class :
    (postnikovCommonRightGammaSourceWitness R hn f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj n hn) =
    postnikovCommonRightGammaToSource R hn f c d ≫
      (postnikovCommonRightFixedMappedClassWitness R hn f c d hj).hom := by
  change (postnikovCommonRightGammaToSource R hn f c d ≫ _) ≫ _ = _
  rw [Category.assoc, postnikovCommonRightFixedMappedSourceWitness_class]

lemma postnikovCommonRightGammaSourceWitness_projection :
    (postnikovCommonRightGammaSourceWitness R hn f c d hj).hom ≫
      Path.map R (postnikovPerturbedProjection R (B.obj j).obj n hn) =
        (postnikovCommonRightGammaBasePath R hn f c d hj).hom := by
  change (postnikovCommonRightGammaToSource R hn f c d ≫ _) ≫ _ = _
  rw [Category.assoc, postnikovCommonRightFixedMappedSourceWitness_projection,
    ← Category.assoc, postnikovCommonRightGammaToSource_projection]
  rfl

lemma postnikovCommonRightGammaBasePath_zero :
    (postnikovCommonRightGammaBasePath R hn f c d hj).hom ≫
      Path.map R (postnikovTransition R (B.obj j).obj n 0 (by omega)) =
    ((postnikovCommonRightGammaBasePath R hn f c d hj).hom ≫
      Path.source R (postnikov R (B.obj j).obj n) ≫
        postnikovTransition R (B.obj j).obj n 0 (by omega)) ≫
          Path.diagonal R (postnikov R (B.obj j).obj 0) := by
  have : (postnikov R (B.obj j).obj 0).X.IsStrictlyGE 0 := by
    simpa only [neg_zero] using postnikov_lowerBound R (B.obj j).obj 0
  have h := Path.map_to_discrete_constant R
    ((postnikovCommonRightGammaBasePath R hn f c d hj).hom ≫
      Path.map R (postnikovTransition R (B.obj j).obj n 0 (by omega)))
  simpa only [Category.assoc, Path.map_source] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
