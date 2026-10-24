module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreZeroRight
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n) {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  (d : ZeroInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

local instance zeroRight_apex_nonpositive : (c.refine R d.source_le).roof.apex.X.IsStrictlyLE 0 :=
  (c.refine R d.source_le).roof_nonpositive

def postnikovCommonZeroRightLayer :
    Bimod (postnikov R (c.refine R d.source_le).roof.apex 0)
      (postnikov R (c.refine R d.source_le).roof.apex 0) :=
  bimoduleRestrict
    (PostnikovRoofZeroSpan.denominator R n hn f (c.refine R d.source_le) ≫
      postnikovMap R (B.transition (d.inverse_le.trans d.stage_le)).hom 0)
    (postnikovLayerZeroBimodule R (B.obj i).obj n)

def postnikovCommonZeroRightNumeratorMap :
    zeroNumeratorLayer R hn f (c.refine R d.source_le) ⟶
      postnikovCommonZeroRightLayer R hn f c d :=
  bimoduleRestrictOver _ _ _ (postnikovCommonZeroInverse_right_base R hn f c d)
    (postnikovLayerZeroMap R (f.app i).hom n)

lemma postnikovCommonZeroRightNumeratorMap_hom :
    (postnikovCommonZeroRightNumeratorMap R hn f c d).hom =
      postnikovLayerMap R (f.app i).hom n := bimoduleRestrictOver_hom _ _ _ _ _

def postnikovCommonZeroRightDenominatorMap :
    zeroDenominatorLayer R hn f (c.refine R d.source_le) ⟶
      postnikovCommonZeroRightLayer R hn f c d :=
  bimoduleRestrictOver _ _ _ rfl
    (postnikovLayerZeroMap R (B.transition (d.inverse_le.trans d.stage_le)).hom n)

lemma postnikovCommonZeroRightDenominatorMap_hom :
    (postnikovCommonZeroRightDenominatorMap R hn f c d).hom =
      postnikovLayerMap R (B.transition (d.inverse_le.trans d.stage_le)).hom n :=
  bimoduleRestrictOver_hom _ _ _ _ _

lemma postnikovCommonZeroRight_coefficient : d.coefficient ≫
    postnikovCommonZeroRightNumeratorMap R hn f c d =
      postnikovCommonZeroRightDenominatorMap R hn f c d := by
  apply Bimod.Hom.ext
  exact (Bimod.comp_hom' _ _).trans
    ((congrArg (fun t => d.coefficient.hom ≫ t)
      (postnikovCommonZeroRightNumeratorMap_hom R hn f c d)).trans
        (d.right_coefficient.trans (postnikovCommonZeroRightDenominatorMap_hom R hn f c d).symm))

lemma postnikovCommonZeroRight_shiftedCoefficient (s : ℤ) :
    DGBimoduleShift.map d.coefficient s ≫
      DGBimoduleShift.map (postnikovCommonZeroRightNumeratorMap R hn f c d) s =
        DGBimoduleShift.map (postnikovCommonZeroRightDenominatorMap R hn f c d) s :=
  ((DGBimoduleShift.functor _ s).map_comp _ _).symm.trans
    (congrArg (fun t => (DGBimoduleShift.functor _ s).map t)
      (postnikovCommonZeroRight_coefficient R hn f c d))

lemma postnikovCommonZeroRight_squareZero (s : ℤ) :
    SquareZero.coefficientMap _ (DGBimoduleShift.map d.coefficient s) ≫
      SquareZero.coefficientMap _
        (DGBimoduleShift.map (postnikovCommonZeroRightNumeratorMap R hn f c d) s) =
    SquareZero.coefficientMap _
      (DGBimoduleShift.map (postnikovCommonZeroRightDenominatorMap R hn f c d) s) :=
  (SquareZero.coefficientMap_comp _ _).trans
    (congrArg (fun t => SquareZero.coefficientMap _ t)
      (postnikovCommonZeroRight_shiftedCoefficient R hn f c d s))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
