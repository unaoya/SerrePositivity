module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaBImagePath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroAffineRefinement

/-!
概要：元の Γ 源上の A 遷移≫fⱼの零底 affine 経路を、元の二 ImageWitness の合成で表示する。
方針：因子分解経路の実同定を前合成し、係数同型の逆と元の零底同型で後合成する。
規約：新しい経路を選ばない。使われ方：native 標準経路と fⱼ の自然性 の境界経路との照合。
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

def postnikovCommonRightViaAImageComposite :=
  postnikovCellImageComposite R (A.obj i).obj (A.obj j).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (A.transition hj).hom (f.app j).hom

def postnikovCommonRightViaAImageIso :=
  postnikovCellFactorizationImageIso R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj
    (A.transition hj).hom (f.app j).hom rfl

def postnikovCommonRightViaAImageToZero :=
  (postnikovCommonRightViaAImageIso R hn f c d hj).inv ≫
    (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom

/-- 元の零底 Γ 経路は、指定した二自然性経路の affine 合成の同じ像に厳密に一致。 -/
lemma postnikovCommonRightZeroAffineViaA_image_hom :
    (postnikovCommonRightZeroAffineViaA R hn f c d hj).hom =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCommonRightViaAImageComposite R hn f c d hj).hom ≫
        Path.map R (postnikovCommonRightViaAImageToZero R hn f c d hj) := by
  change ((postnikovCommonRightToFactorization R hn f c d ≫
    (postnikovCellFactorizationAffineCommonWitness R (A.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.numerator
      (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj
      (A.transition hj).hom (f.app j).hom
      rfl).hom) ≫
      Path.map R (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom) = _
  rw [postnikovCellFactorizationImagePath_inv_hom]
  simp only [postnikovCommonRightImageToSecond, postnikovCommonRightViaAImageComposite,
    postnikovCommonRightViaAImageToZero, postnikovCommonRightViaAImageIso,
    Path.map_comp, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
