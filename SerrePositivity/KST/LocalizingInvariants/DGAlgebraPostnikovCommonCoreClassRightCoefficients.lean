module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightCoefficientBase

/-!
概要：fⱼ と直接 B 遷移の実係数射を、元の P 上の同じ classifying 双加群へ構成する。
方針：元の層射を零底係数へ移し、底射の厳密な等式で係数表示を揃える。
規約：実双加群射と元の underlying 層射を保持。使われ方：fixed 模型射の右係数三角形。
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

def postnikovCommonClassRightTargetCoefficient :
    postnikovCommonClassTransitionLayer R hn f c d hj ⟶
      postnikovCommonRightClassifyingLayer R hn f c d hj :=
  postnikovCellClassOverCoefficient R (A.obj j).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (postnikovCommonClassRetractBase R hn f c d (hj := hj)) (f.app j).hom ≫
  postnikovClassBaseZeroCoefficient R (B.obj j).obj (postnikovCommonClassBase R hn f c d)
    n hn 1 (postnikovCommonClassRightImageBase R hn f c d hj) ≫
  (bimoduleRestrictBaseEqIso (postnikovCommonClassRightImageBase_zero R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)).hom

def postnikovCommonClassRightDenominatorCoefficient :
    roofShiftedDenominatorLayer R hn f
      (roofRefine R hn f c d.zero.source_le) 1 ⟶
      postnikovCommonRightClassifyingLayer R hn f c d hj :=
  postnikovCellClassOverCoefficient R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R hn f c d hj) ≫
  postnikovClassBaseZeroCoefficient R (B.obj j).obj (postnikovCommonClassBase R hn f c d)
    n hn 1 (postnikovCommonClassRightDenominatorBase R hn f c d hj) ≫
  (bimoduleRestrictBaseEqIso (postnikovCommonClassRightDenominatorBase_zero R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)).hom

lemma postnikovCommonClassRightTargetCoefficient_hom :
    (postnikovCommonClassRightTargetCoefficient R hn f c d hj).hom =
      (postnikovLayerMap R (f.app j).hom n)⟦(1 : ℤ)⟧' := by
  simp only [postnikovCommonClassRightTargetCoefficient, Bimod.comp_hom',
    postnikovCellClassOverCoefficient_hom, postnikovClassBaseZeroCoefficient_hom,
    bimoduleRestrictBaseEqIso_hom]
  change (postnikovLayerMap R (f.app j).hom n)⟦(1 : ℤ)⟧' ≫
    𝟙 ((postnikovLayer R (B.obj j).obj n)⟦(1 : ℤ)⟧) ≫
    𝟙 ((postnikovLayer R (B.obj j).obj n)⟦(1 : ℤ)⟧) = _
  simp only [Category.comp_id]

lemma postnikovCommonClassRightDenominatorCoefficient_hom :
    (postnikovCommonClassRightDenominatorCoefficient R hn f c d hj).hom =
      (postnikovLayerMap R (postnikovCommonRightDenDirectMap R hn f c d hj) n)⟦(1 : ℤ)⟧' := by
  simp only [postnikovCommonClassRightDenominatorCoefficient, Bimod.comp_hom',
    postnikovCellClassOverCoefficient_hom, postnikovClassBaseZeroCoefficient_hom,
    bimoduleRestrictBaseEqIso_hom]
  change (postnikovLayerMap R (postnikovCommonRightDenDirectMap R hn f c d hj) n)⟦(1 : ℤ)⟧' ≫
    𝟙 ((postnikovLayer R (B.obj j).obj n)⟦(1 : ℤ)⟧) ≫
    𝟙 ((postnikovLayer R (B.obj j).obj n)⟦(1 : ℤ)⟧) = _
  simp only [Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
