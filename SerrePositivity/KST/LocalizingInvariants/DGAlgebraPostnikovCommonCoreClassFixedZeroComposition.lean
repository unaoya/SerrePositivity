module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedZeroPaths
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeReverseCongr

/-!
概要：fixed Γ の右 class 像を反転と標準像の実 affine 合成として同定する。
方針：前合成・底付き移送による反転合成の保存を元の二経路へ適用する。
規約：線形式だけでなく全乗法的経路を比較。使われ方：元の自然性二重経路への接続。
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
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonClassFixedCompatibilityMapped_hom :
    (postnikovCommonClassFixedCompatibilityMappedRelative R hn f c d hj e).hom =
      ((postnikovCommonClassFixedTransitionMappedRelative R hn f c d hj e).reverse.comp
        (postnikovCommonClassFixedStandardMappedRelative R hn f c d hj)).hom := by
  exact SquareZero.RelativeWitness.precomp_mapOver_reverse_comp_hom
    (postnikovCommonClassFixedTransitionRelative R hn f c d e)
    (postnikovCommonClassStandardRelative R hn f c d (hj := hj))
    (cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d))
    (postnikovCommonClassFixedZeroBase R hn f c d hj)
    (postnikovCommonClassFixedZeroMap R hn f c d hj)
    (postnikovCommonClassFixedZeroMap_projection R hn f c d hj)

lemma postnikovCommonClassFixedTransitionMapped_glue :
    (postnikovCommonClassFixedTransitionMappedRelative R hn f c d hj e).hom =
      (postnikovCommonRightGlueZeroRelative R hn f c d hj).hom :=
  postnikovCommonClassFixedTransitionZeroRight_hom R hn f c d hj e

lemma postnikovCommonClassFixedTransitionMapped_reverse_glue :
    (postnikovCommonClassFixedTransitionMappedRelative R hn f c d hj e).reverse.hom =
      (postnikovCommonRightGlueZeroRelative R hn f c d hj).reverse.hom :=
  SquareZero.RelativeWitness.reverse_congr_hom_of_paths
    (postnikovCommonClassFixedTransitionMapped_glue R hn f c d hj e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
