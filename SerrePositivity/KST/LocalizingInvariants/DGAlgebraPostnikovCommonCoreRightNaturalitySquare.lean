module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassCompositionCongr
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardSquare

/-!
概要：元の f の自然性正方形の二つの因子分解に、同じ直接 class 経路を与える。
方針：A の遷移と f、f と B の遷移の合成が一致する元の自然性を使う。
規約：同じ元の分子・共通底を保つ。使われ方：Γ の右側の二つの経路比較の基準。
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

lemma postnikovCommonRightNaturalitySquare_direct :
    (postnikovCellCompositionClassDirect R (A.obj i).obj (A.obj j).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.numerator
      (A.transition hj).hom (f.app j).hom).hom =
    (postnikovCellCompositionClassDirect R (A.obj i).obj (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.numerator
      (f.app i).hom (B.transition hj).hom).hom := by
  apply postnikovCellCompositionClassDirect_hom_congr
  exact congrArg (fun t => t.hom) (f.naturality hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
