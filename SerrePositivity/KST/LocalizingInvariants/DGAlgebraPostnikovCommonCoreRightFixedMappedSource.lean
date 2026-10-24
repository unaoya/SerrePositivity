module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedNaturality

/-!
概要：元の W の class 経路を生む、摂動代数への実 source 経路を取り出す。
方針：指定した fixed cell 経路に元の cell lift を後合成する。
規約：元の class 全経路と動く底を回収。使われ方：native 模型内の W 比較。
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
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightFixedMappedSourceWitness :=
  (cellPathNonpositiveFixedWitness R ((postnikovCommonRightBasePath R hn f c d).postcomp
    (postnikovMap R (B.transition hj).hom n))).postcomp
      (postnikovCellLift R (B.obj j).obj n hn)

lemma postnikovCommonRightFixedMappedSourceWitness_class :
    (postnikovCommonRightFixedMappedSourceWitness R hn f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj n hn) =
        (postnikovCommonRightFixedMappedClassWitness R hn f c d hj).hom := by
  change ((cellPathNonpositiveFixedWitness R
    ((postnikovCommonRightBasePath R hn f c d).postcomp
      (postnikovMap R (B.transition hj).hom n))).hom ≫
        Path.map R (postnikovCellLift R (B.obj j).obj n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp]
  rfl

lemma postnikovCommonRightFixedMappedSourceWitness_projection :
    (postnikovCommonRightFixedMappedSourceWitness R hn f c d hj).hom ≫
      Path.map R (postnikovPerturbedProjection R (B.obj j).obj n hn) =
        postnikovCommonRightCellProjection R hn f c d ≫
          ((postnikovCommonRightBasePath R hn f c d).postcomp
            (postnikovMap R (B.transition hj).hom n)).hom := by
  change ((cellPathNonpositiveFixedWitness R
    ((postnikovCommonRightBasePath R hn f c d).postcomp
      (postnikovMap R (B.transition hj).hom n))).hom ≫
        Path.map R (postnikovCellLift R (B.obj j).obj n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCellLift_projection,
    cellPathNonpositiveFixedWitness_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
