module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCompositeZeroCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

/-!
概要：合成自然性の実平方零標的を、classifying 側の同じ零底標的へ写す同型。
方針：underlying 恒等の係数同型を平方零関手で写し、元の二つの射影を比較する。
規約：全 class 標的への射も保持。使われ方：全経路の零底への移送と照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightCompositeZeroIso :
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj) ≅
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonRightClassifyingLayer R hn f c d hj) :=
  SquareZero.coefficientIso _ (postnikovCommonRightCompositeZeroCoefficientIso R hn f c d hj)

lemma postnikovCommonRightCompositeZeroIso_projection :
    (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ := SquareZero.coefficientMap_projection _ _

lemma postnikovCommonRightCompositeZeroIso_inv_projection :
    (postnikovCommonRightCompositeZeroIso R hn f c d hj).inv ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ := SquareZero.coefficientMap_projection _ _

lemma postnikovCommonRightCompositeZeroIso_hom :
    (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom.hom =
      biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X)
        (𝟙 ((postnikovLayer R (B.obj j).obj n)⟦(1 : ℤ)⟧)) := by
  rw [postnikovCommonRightCompositeZeroIso, SquareZero.coefficientIso_hom,
    SquareZero.coefficientMap_hom, postnikovCommonRightCompositeZeroCoefficientIso_hom]
  rfl

/-- 底変更した class 標的への全射も元の零切断射と厳密に一致する。 -/
lemma postnikovCommonRightCompositeZeroIso_map :
    (postnikovCommonRightCompositeZeroIso R hn f c d hj).hom ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1) =
    SquareZero.baseChangeMap
      ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) n)
      (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1) ≫
        postnikovClassToZeroBase R (B.obj j).obj n hn 1 := by
  apply Mon.Hom.ext
  rw [Mon.comp_hom', Mon.comp_hom', postnikovCommonRightCompositeZeroIso_hom,
    SquareZero.baseChangeMap_hom, SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom]
  change biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X)
      (𝟙 ((postnikovLayer R (B.obj j).obj n)⟦(1 : ℤ)⟧)) ≫
    biprod.map (postnikovCommonRightClassifyingBase R hn f c d hj).hom (𝟙 _) =
    biprod.map (((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) n).hom) (𝟙 _) ≫
    biprod.map (postnikovTransition R (B.obj j).obj n 0 (by omega)).hom (𝟙 _)
  apply biprod.hom_ext <;> simp [Category.assoc, ← Mon.comp_hom',
    postnikovCommonRightComposite_zero_base R hn f c d hj]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
