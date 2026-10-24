module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenDirectRestored
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageZeroMap

/-!
概要：比較に使う直接経路の零 class 像が、元の直接 B 遷移の自然性そのものと示す。
方針：元の単一 ImageWitness の二射影と、係数射の全合成式を使う。
規約：比較用の任意経路に置き換えない。使われ方：元の直接遷移の右模型照合。
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
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonRightDenDirectPath_map :
    (postnikovCommonRightDenDirectPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCellClassOverNaturalityWitness R (B.obj d.zero.stage).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (roofRefine R hn f c d.zero.source_le).roof.denominator
        (postnikovCommonRightDenDirectMap R hn f c d hj)).hom ≫
      Path.map R (postnikovClassToZeroBase R (B.obj j).obj n hn 1) := by
  let k := SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
  let v := postnikovCellImageRelative R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R hn f c d hj)
  let a := postnikovCommonRightImageToSecond R hn f c d
  let h₁ := congrArg (fun t => t ≫ Path.map R k)
    (postnikovCommonRightDenDirectPath_hom R hn f c d hj)
  let h₂ := Path.map_post_whisker R a v.hom
    (postnikovCommonRightDenDirectToZero R hn f c d hj) k
  let h₃ := congrArg (fun t => a ≫ (v.hom ≫ Path.map R t))
    (postnikovCommonRightDenDirectToZero_map R hn f c d hj)
  let h₄ := congrArg (fun t => a ≫ t)
    (postnikovCellImageRelative_zero_map R (B.obj d.zero.stage).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.denominator
      (postnikovCommonRightDenDirectMap R hn f c d hj))
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
