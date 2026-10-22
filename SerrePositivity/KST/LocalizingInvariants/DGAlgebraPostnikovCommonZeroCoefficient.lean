module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonZeroBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerInverseRefinement

/-!
概要：元の roof と一致する共通零底上に、元の層遷移と係数逆を合成した実射を構成。
方針：底を変える実双加群射を、証明済みの底の厳密な三角形に沿って制限する。
規約：元の係数射・両 cochain 三角形を保持。使われ方：元の共通底上への作用の移送。
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
variable (R : Type u) [CommRing R] (n : ℤ) {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

def postnikovCommonZeroDenominatorLayer :
    Bimod (postnikovOneRoofZeroBase R f c) (postnikovOneRoofZeroBase R f c) :=
  bimoduleRestrict (postnikovOneRoofZeroDenominator R f c)
    (postnikovLayerZeroBimodule R (B.obj m).obj n)

def postnikovCommonZeroNumeratorLayer :
    Bimod (postnikovOneRoofZeroBase R f c) (postnikovOneRoofZeroBase R f c) :=
  bimoduleRestrict (postnikovOneRoofZeroNumerator R f c)
    (postnikovLayerZeroBimodule R (A.obj i).obj n)

variable {l : ℕ} {hj : i ≤ l} (e : PostnikovZeroLayerInverse R n f i l hj)
  {k : ℕ} (hm : m ≤ k) (hl : l ≤ k)
  (hb : postnikovOneRoofZeroNumerator R f (postnikovOneRoofRefine R f c hm) =
    postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c hm) ≫
      postnikovMap R (B.transition hl).hom 0 ≫ e.base)

def postnikovCommonZeroCoefficientMap :
    postnikovCommonZeroDenominatorLayer R n f (postnikovOneRoofRefine R f c hm) ⟶
      postnikovCommonZeroNumeratorLayer R n f (postnikovOneRoofRefine R f c hm) :=
  bimoduleRestrictOver
    (postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c hm))
    (postnikovOneRoofZeroNumerator R f (postnikovOneRoofRefine R f c hm))
    (postnikovMap R (B.transition hl).hom 0 ≫ e.base) hb.symm
    (PostnikovZeroLayerInverse.refinedCoefficient R e hl)

lemma postnikovCommonZeroCoefficientMap_refined_hom :
    (postnikovCommonZeroCoefficientMap R n f c e hm hl hb).hom =
      (PostnikovZeroLayerInverse.refinedCoefficient R e hl).hom :=
  bimoduleRestrictOver_hom _ _ _ _ _

lemma postnikovCommonZeroCoefficientMap_hom :
    (postnikovCommonZeroCoefficientMap R n f c e hm hl hb).hom =
      postnikovLayerMap R (B.transition hl).hom n ≫ e.coefficient.hom :=
  (postnikovCommonZeroCoefficientMap_refined_hom R n f c e hm hl hb).trans
    (PostnikovZeroLayerInverse.refinedCoefficient_hom R e hl)

lemma postnikovCommonZeroCoefficientMap_left : postnikovLayerMap R (f.app k).hom n ≫
    (postnikovCommonZeroCoefficientMap R n f c e hm hl hb).hom =
      postnikovLayerMap R (A.transition (hj.trans hl)).hom n :=
  (congrArg (fun t => postnikovLayerMap R (f.app k).hom n ≫ t)
    (postnikovCommonZeroCoefficientMap_refined_hom R n f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_left R e hl)

lemma postnikovCommonZeroCoefficientMap_right :
    (postnikovCommonZeroCoefficientMap R n f c e hm hl hb).hom ≫
      postnikovLayerMap R (f.app i).hom n =
        postnikovLayerMap R (B.transition (hj.trans hl)).hom n :=
  (congrArg (fun t => t ≫ postnikovLayerMap R (f.app i).hom n)
    (postnikovCommonZeroCoefficientMap_refined_hom R n f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_right R e hl)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
