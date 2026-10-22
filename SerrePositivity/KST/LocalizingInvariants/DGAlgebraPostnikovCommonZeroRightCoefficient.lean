module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonZeroRight
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionOver
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientComposition

/-!
概要：同じ共通零底上に右係数三角形を実双加群射・平方零代数射で構成する。
方針：厳密な右底三角形に沿って元の二つの層射を制限し、元の係数三角形で照合する。
規約：指定した逆・細分・遷移を保持。使われ方：class の像の比較。
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
variable (R : Type u) [CommRing R] (n : ℤ) {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonZeroInverse R n f c)

def postnikovCommonZeroRightLayer :
    Bimod (postnikovOneRoofZeroBase R f (postnikovOneRoofRefine R f c d.source_le))
      (postnikovOneRoofZeroBase R f (postnikovOneRoofRefine R f c d.source_le)) :=
  bimoduleRestrict
    (postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c d.source_le) ≫
      postnikovMap R (B.transition (d.inverse_le.trans d.stage_le)).hom 0)
    (postnikovLayerZeroBimodule R (B.obj i).obj n)

def postnikovCommonZeroRightNumeratorMap :
    postnikovCommonZeroNumeratorLayer R n f (postnikovOneRoofRefine R f c d.source_le) ⟶
      postnikovCommonZeroRightLayer R n f c d :=
  bimoduleRestrictOver _ _ _ (postnikovCommonZeroInverse_right_base R n f c d)
    (postnikovLayerZeroMap R (f.app i).hom n)

lemma postnikovCommonZeroRightNumeratorMap_hom :
    (postnikovCommonZeroRightNumeratorMap R n f c d).hom =
      postnikovLayerMap R (f.app i).hom n := bimoduleRestrictOver_hom _ _ _ _ _

def postnikovCommonZeroRightDenominatorMap :
    postnikovCommonZeroDenominatorLayer R n f (postnikovOneRoofRefine R f c d.source_le) ⟶
      postnikovCommonZeroRightLayer R n f c d :=
  bimoduleRestrictOver _ _ _ rfl
    (postnikovLayerZeroMap R (B.transition (d.inverse_le.trans d.stage_le)).hom n)

lemma postnikovCommonZeroRightDenominatorMap_hom :
    (postnikovCommonZeroRightDenominatorMap R n f c d).hom =
      postnikovLayerMap R (B.transition (d.inverse_le.trans d.stage_le)).hom n :=
  bimoduleRestrictOver_hom _ _ _ _ _

lemma postnikovCommonZeroRight_coefficient : d.coefficient ≫
    postnikovCommonZeroRightNumeratorMap R n f c d =
      postnikovCommonZeroRightDenominatorMap R n f c d := by
  apply Bimod.Hom.ext
  exact (Bimod.comp_hom' _ _).trans
    ((congrArg (fun t => d.coefficient.hom ≫ t)
      (postnikovCommonZeroRightNumeratorMap_hom R n f c d)).trans
        (d.right_coefficient.trans (postnikovCommonZeroRightDenominatorMap_hom R n f c d).symm))

lemma postnikovCommonZeroRight_shiftedCoefficient (s : ℤ) :
    DGBimoduleShift.map d.coefficient s ≫
      DGBimoduleShift.map (postnikovCommonZeroRightNumeratorMap R n f c d) s =
        DGBimoduleShift.map (postnikovCommonZeroRightDenominatorMap R n f c d) s :=
  ((DGBimoduleShift.functor _ s).map_comp _ _).symm.trans
    (congrArg (fun t => (DGBimoduleShift.functor _ s).map t)
      (postnikovCommonZeroRight_coefficient R n f c d))

lemma postnikovCommonZeroRight_squareZero (s : ℤ) :
    SquareZero.coefficientMap _ (DGBimoduleShift.map d.coefficient s) ≫
      SquareZero.coefficientMap _
        (DGBimoduleShift.map (postnikovCommonZeroRightNumeratorMap R n f c d) s) =
    SquareZero.coefficientMap _
      (DGBimoduleShift.map (postnikovCommonZeroRightDenominatorMap R n f c d) s) :=
  (SquareZero.coefficientMap_comp _ _).trans
    (congrArg (fun t => SquareZero.coefficientMap _ t)
      (postnikovCommonZeroRight_shiftedCoefficient R n f c d s))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
