module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofCommonZeroBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerInverseRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerFromZero

/-!
概要：任意の有限段の細分 roof 上に、元の層逆を左右作用と両 cochain 三角形付きで戻す。
方針：共通零底の厳密式で制限した係数を、元の層の零制限同型で共通底へ移す。
規約：元の underlying 係数射を保持。使われ方：高次 Postnikov class の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovRoofZeroSpan
open ProExcision
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  {l : ℕ} {hj : i ≤ l} (e : PostnikovZeroLayerInverse R n f i l hj)
  {k : ℕ} (hm : m ≤ k) (hl : l ≤ k)

attribute [local instance] original_apex_nonpositive refined_apex_nonpositive
  refined_source_nonpositive refined_target_nonpositive

variable (hb : numerator R n hn f (c.refine R hm) =
    denominator R n hn f (c.refine R hm) ≫ postnikovMap R (B.transition hl).hom 0 ≫ e.base)

def zeroCoefficient :
    bimoduleRestrict (denominator R n hn f (c.refine R hm))
      (postnikovLayerZeroBimodule R (B.obj k).obj n) ⟶
    bimoduleRestrict (numerator R n hn f (c.refine R hm))
      (postnikovLayerZeroBimodule R (A.obj i).obj n) :=
  bimoduleRestrictOver (denominator R n hn f (c.refine R hm))
    (numerator R n hn f (c.refine R hm)) (postnikovMap R (B.transition hl).hom 0 ≫ e.base)
    hb.symm (PostnikovZeroLayerInverse.refinedCoefficient R e hl)

lemma zeroCoefficient_refined_hom : (zeroCoefficient R n hn f c e hm hl hb).hom =
    (PostnikovZeroLayerInverse.refinedCoefficient R e hl).hom :=
  bimoduleRestrictOver_hom _ _ _ _ _

lemma zeroCoefficient_hom : (zeroCoefficient R n hn f c e hm hl hb).hom =
    postnikovLayerMap R (B.transition hl).hom n ≫ e.coefficient.hom :=
  (zeroCoefficient_refined_hom R n hn f c e hm hl hb).trans
    (PostnikovZeroLayerInverse.refinedCoefficient_hom R e hl)

lemma zeroCoefficient_left : postnikovLayerMap R (f.app k).hom n ≫
    (zeroCoefficient R n hn f c e hm hl hb).hom =
      postnikovLayerMap R (A.transition (hj.trans hl)).hom n :=
  (congrArg (fun t => postnikovLayerMap R (f.app k).hom n ≫ t)
    (zeroCoefficient_refined_hom R n hn f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_left R e hl)

lemma zeroCoefficient_right : (zeroCoefficient R n hn f c e hm hl hb).hom ≫
    postnikovLayerMap R (f.app i).hom n =
      postnikovLayerMap R (B.transition (hj.trans hl)).hom n :=
  (congrArg (fun t => t ≫ postnikovLayerMap R (f.app i).hom n)
    (zeroCoefficient_refined_hom R n hn f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_right R e hl)

def coefficient :
    bimoduleRestrict (c.refine R hm).roof.denominator
      (postnikovLayerBaseBimodule R (B.obj k).obj n hn) ⟶
    bimoduleRestrict (c.refine R hm).roof.numerator
      (postnikovLayerBaseBimodule R (A.obj i).obj n hn) :=
  postnikovLayerFromZero R (B.obj k).obj (A.obj i).obj (c.refine R hm).roof.apex n hn
    (c.refine R hm).roof.denominator (c.refine R hm).roof.numerator
    (zeroCoefficient R n hn f c e hm hl hb)

lemma coefficient_refined_hom : (coefficient R n hn f c e hm hl hb).hom =
    (PostnikovZeroLayerInverse.refinedCoefficient R e hl).hom :=
  (postnikovLayerFromZero_hom R (B.obj k).obj (A.obj i).obj (c.refine R hm).roof.apex
    n hn (c.refine R hm).roof.denominator (c.refine R hm).roof.numerator _).trans
      (bimoduleRestrictOver_hom _ _ _ _ _)

lemma coefficient_hom : (coefficient R n hn f c e hm hl hb).hom =
    postnikovLayerMap R (B.transition hl).hom n ≫ e.coefficient.hom :=
  (coefficient_refined_hom R n hn f c e hm hl hb).trans
    (PostnikovZeroLayerInverse.refinedCoefficient_hom R e hl)

lemma coefficient_left : postnikovLayerMap R (f.app k).hom n ≫
    (coefficient R n hn f c e hm hl hb).hom =
      postnikovLayerMap R (A.transition (hj.trans hl)).hom n :=
  (congrArg (fun t => postnikovLayerMap R (f.app k).hom n ≫ t)
    (coefficient_refined_hom R n hn f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_left R e hl)

lemma coefficient_right : (coefficient R n hn f c e hm hl hb).hom ≫
    postnikovLayerMap R (f.app i).hom n =
      postnikovLayerMap R (B.transition (hj.trans hl)).hom n :=
  (congrArg (fun t => t ≫ postnikovLayerMap R (f.app i).hom n)
    (coefficient_refined_hom R n hn f c e hm hl hb)).trans
      (PostnikovZeroLayerInverse.refinedCoefficient_right R e hl)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovRoofZeroSpan
