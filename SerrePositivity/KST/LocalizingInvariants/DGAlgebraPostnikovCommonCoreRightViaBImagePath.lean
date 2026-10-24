module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationImagePath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroAffineRefinement

/-!
概要：元の Γ 源上の fᵢ≫B 遷移の零底 affine 経路を、元の二 ImageWitness の合成で表示する。
方針：因子分解経路の実同定を前合成し、係数同型の逆と元の零底同型で後合成する。
規約：新しい経路を選ばない。使われ方：元の T′・L・W の境界経路との照合。
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

def postnikovCommonRightImageToSecond := postnikovCommonRightToFactorization R hn f c d ≫
  postnikovCellImageToSecond R (postnikovCommonClassBase R hn f c d)

/-- 同じ Γ 源の二重 cell 射は、元の貼合せの前合成と厳密に一致する。 -/
lemma postnikovCommonRightImageToSecond_eq : postnikovCommonRightImageToSecond R hn f c d =
    (postnikovCommonRightToClassifying R hn f c d ≫
      cellAugmentation R (postnikovCommonRightCellSource R hn f c d)) ≫
      cellPathNonpositiveToDoubleCell R (postnikovCommonClassBase R hn f c d) := by
  simp only [postnikovCommonRightImageToSecond, postnikovCommonRightToFactorization,
    postnikovCommonRightToClassifying, Category.assoc,
    reassoc_of% cellPathNonpositiveToCell_projection,
    postnikovCellImageToSecond, cellFixedNonpositiveToFourthCell,
    cellPathNonpositiveToDoubleCell, iteratedCellAugmentation, iteratedCellResolution,
    Category.assoc, Category.comp_id]

def postnikovCommonRightViaBImageComposite :=
  postnikovCellImageComposite R (A.obj i).obj (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (f.app i).hom (B.transition hj).hom

def postnikovCommonRightViaBImageIso :=
  postnikovCellFactorizationImageIso R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (B.obj i).obj
    (f.app i).hom (B.transition hj).hom (congrArg (fun t => t.hom) (f.naturality hj)).symm

def postnikovCommonRightViaBImageToZero :=
  (postnikovCommonRightViaBImageIso R hn f c d hj).inv ≫
    (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom

/-- 元の零底 Γ 経路は、指定した二自然性経路の affine 合成の同じ像に厳密に一致。 -/
lemma postnikovCommonRightZeroAffineViaB_image_hom :
    (postnikovCommonRightZeroAffineViaB R hn f c d hj).hom =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCommonRightViaBImageComposite R hn f c d hj).hom ≫
        Path.map R (postnikovCommonRightViaBImageToZero R hn f c d hj) := by
  change ((postnikovCommonRightToFactorization R hn f c d ≫
    (postnikovCellFactorizationAffineCommonWitness R (A.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.numerator
      (postnikovCommonRightNaturalityComposite R f hj) (B.obj i).obj
      (f.app i).hom (B.transition hj).hom
      (congrArg (fun t => t.hom) (f.naturality hj)).symm).hom) ≫
      Path.map R (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom) = _
  rw [postnikovCellFactorizationImagePath_inv_hom]
  simp only [postnikovCommonRightImageToSecond, postnikovCommonRightViaBImageComposite,
    postnikovCommonRightViaBImageToZero, postnikovCommonRightViaBImageIso,
    Path.map_comp, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
