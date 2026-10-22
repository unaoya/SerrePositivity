module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightAffineCompositeSquare
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionEqualityIso

/-!
概要：二因子分解の合成射の係数を、classifying 比較の元の零底係数へ同定する。
方針：f の自然性で底射を同定し、零切断への既存係数同型と恒等底射移送を合成する。
規約：元の P と underlying 係数恒等射を保持。使われ方：Γ 源上の比較の零底への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

abbrev postnikovCommonRightClassifyingLayer :=
  bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)

lemma postnikovCommonRightComposite_zero_base :
    ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) 1) ≫
        postnikovTransition R (B.obj j).obj 1 0 (by omega) =
      postnikovCommonRightClassifyingBase R f c d hj := by
  have he := congrArg (fun t => t.hom) (f.naturality hj)
  change (A.transition hj).hom ≫ (f.app j).hom =
    (f.app i).hom ≫ (B.transition hj).hom at he
  simp only [postnikovCommonRightNaturalityComposite, he, postnikovMap_composition,
    postnikovCommonRightClassifyingBase, postnikovCommonRightBase, Category.assoc]

def postnikovCommonRightCompositeZeroCoefficientIso :
    postnikovCommonRightNaturalityCompositeLayer R f c d hj ≅
      postnikovCommonRightClassifyingLayer R f c d hj :=
  postnikovClassBaseZeroCoefficientIso R (B.obj j).obj (postnikovCommonClassBase R f c d)
    1 (by omega) 1 ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) 1) ≪≫
    bimoduleRestrictBaseEqIso (postnikovCommonRightComposite_zero_base R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)

lemma postnikovCommonRightCompositeZeroCoefficientIso_hom :
    (postnikovCommonRightCompositeZeroCoefficientIso R f c d hj).hom.hom =
      𝟙 ((postnikovLayer R (B.obj j).obj 1)⟦(1 : ℤ)⟧) := by
  rw [postnikovCommonRightCompositeZeroCoefficientIso, Iso.trans_hom]
  change 𝟙 _ ≫ (bimoduleRestrictBaseEqIso
    (postnikovCommonRightComposite_zero_base R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)).hom.hom = _
  rw [bimoduleRestrictBaseEqIso_hom, Category.id_comp]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
