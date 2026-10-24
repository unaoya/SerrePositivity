module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedGlueZeroMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRight

/-!
概要：fixed Γ の native 遷移経路の右像を、元の G の同じ Γ 源上の全経路へ同定する。
方針：元の零底射影と fixed 遷移の厳密な右三角形を、同じ前合成射で写す。
規約：元の fixed Γ と元の G を保持。使われ方：class 互換性と実自然性比較の接続。
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

lemma postnikovCommonRightGlueRefined_fixed_map :
    (postnikovCommonRightGlueRefinedPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
      (postnikovCommonRightFixedClassGlueWitness R hn f c d).hom ≫ Path.map R
        (postnikovCommonRightClassToZero R hn f c d ≫
          postnikovZeroClassMap R n 1 (B.transition hj).hom) := by
  change (postnikovCommonRightToClassifying R hn f c d ≫
    (postnikovCommonRightTransitionLift R hn f c d hj
      (postnikovCommonRightAffineFixedGlue R hn f c d)).hom) ≫ _ = _
  rw [Category.assoc, postnikovCommonRightTransitionLift_map R hn f c d hj
    (postnikovCommonRightAffineFixedGlue R hn f c d), Path.map_comp]
  simp only [Category.assoc,
    reassoc_of% (postnikovCommonRightFixedClassGlueWitness_zero R hn f c d),
    postnikovCommonRightToClassifying, reassoc_of% cellPathNonpositiveToCell_projection,
    postnikovCommonRightFixedZeroGlueWitness, SquareZero.RelativeWitness.precomp_hom]

variable (e : PostnikovZeroLayerInverse R n f j i hj)

def postnikovCommonClassFixedTransitionZeroRightPath :=
  ((postnikovCommonClassFixedTransitionWitness R hn f c d e).precomp
    (cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d))).postcomp
    (postnikovCommonClassTransitionToZero R hn f c d hj ≫
      postnikovZeroClassMap R n 1 (f.app j).hom)

lemma postnikovCommonClassFixedTransitionZeroRight_hom :
    (postnikovCommonClassFixedTransitionZeroRightPath R hn f c d hj e).hom =
    (postnikovCommonRightGlueRefinedPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) := by
  have ht := congrArg (fun k =>
    cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫ k)
    (postnikovCommonClassFixedTransition_zero_right R hn f c d e)
  exact (Category.assoc _ _ _).trans
    (ht.trans (postnikovCommonRightGlueRefined_fixed_map R hn f c d hj).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
