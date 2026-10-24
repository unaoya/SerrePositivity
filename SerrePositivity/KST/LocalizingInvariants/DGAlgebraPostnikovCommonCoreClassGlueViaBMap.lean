module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassGlueStandardBottom

/-!
概要：元の分母比較の右辺の零底像を、同じ G⁻¹・ViaB・W の実合成へ同定する。
方針：底付き移送の反転保存と二回の合成保存を、全経路の等式として使う。
規約：元の G・W と係数射を保持。使われ方：分母比較と native 標準比較の縦合成。
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

def postnikovCommonClassGlueSolvedMappedPath :=
  (postnikovCommonRightGlueSolvedPath R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)

lemma postnikovCommonClassGlueViaB_map_hom :
    (postnikovCommonClassGlueSolvedMappedPath R hn f c d hj).hom =
      (postnikovCommonClassGlueViaBBottom R hn f c d hj).hom := by
  let k := SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
  let hk := SquareZero.baseChangeMap_projection
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
  let g := postnikovCommonRightGlueRefinedPath R hn f c d hj
  let v := postnikovCommonRightViaBContourPath R hn f c d hj
  let w := postnikovCommonRightContourBottomRefinedPath R hn f c d hj
  have hm := SquareZero.RelativeWitness.mapOver_comp_hom
    (postnikovCommonRightClassifyingBase R hn f c d hj) k hk g.reverse (v.comp w)
  have hr := SquareZero.RelativeWitness.mapOver_reverse_hom
    (postnikovCommonRightClassifyingBase R hn f c d hj) k hk g
  have hb := SquareZero.RelativeWitness.mapOver_comp_hom
    (postnikovCommonRightClassifyingBase R hn f c d hj) k hk v w
  exact hm.trans (SquareZero.RelativeWitness.comp_congr_hom_of_paths hr hb)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
