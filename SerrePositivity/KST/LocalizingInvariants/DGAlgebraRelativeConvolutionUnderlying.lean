module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeConvolutionRestriction
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionConstantComparison

/-!
概要：実相対 AW 制限の底を、元の複体の内部 Hom pullback と同定する。
方針：代数の忘却関手の極限保存と、元の前合成・後合成との等式を使う。
規約：底の比較同型は実 pullback の両射影を保持する。
使われ方：E2 の相対内部 Hom の性質を、同じ実代数制限射へ適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {X B : Mon (Complex R)}
  (q : X ⟶ B) {K L : SSet.{0}} (f : K ⟶ L)

lemma simplicialConvolutionTargetNatTrans_hom :
    ((simplicialConvolutionTargetNatTrans R q).app (op K)).hom =
      homPostcompose (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains R K) q.hom := rfl

lemma simplicialConvolutionRestriction_hom :
    ((simplicialConvolution R X).map f.op).hom =
      homPrecompose ((EInfinity.BarrattEccles.normalizedFunctor R).map f) X.X := by
  change ((MonoidalClosed.pre ((EInfinity.BarrattEccles.normalizedFunctor R).map f)).app X.X) = _
  exact convolutionPre_eq_homPrecompose R _ _

lemma relativeConvolutionRestriction_original_isPullback :
    IsPullback (relativeConvolutionRestrictionFst R q f).hom
      (relativeConvolutionRestrictionSnd R q f).hom
      (homPostcompose (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains R K) q.hom)
      (homPrecompose ((EInfinity.BarrattEccles.normalizedFunctor R).map f) B.X) := by
  have h := relativeConvolutionRestriction_underlying_isPullback R q f
  rw [simplicialConvolutionTargetNatTrans_hom, simplicialConvolutionRestriction_hom] at h
  exact h

def relativeConvolutionRestrictionUnderlyingIso :
    (relativeConvolutionRestrictionTarget R q f).X ≅
      pullback (homPostcompose (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains R K) q.hom)
        (homPrecompose ((EInfinity.BarrattEccles.normalizedFunctor R).map f) B.X) :=
  (relativeConvolutionRestriction_original_isPullback R q f).isoPullback

@[reassoc]
lemma relativeConvolutionRestrictionUnderlyingIso_fst :
    (relativeConvolutionRestrictionUnderlyingIso R q f).hom ≫ pullback.fst _ _ =
      (relativeConvolutionRestrictionFst R q f).hom :=
  (relativeConvolutionRestriction_original_isPullback R q f).isoPullback_hom_fst

@[reassoc]
lemma relativeConvolutionRestrictionUnderlyingIso_snd :
    (relativeConvolutionRestrictionUnderlyingIso R q f).hom ≫ pullback.snd _ _ =
      (relativeConvolutionRestrictionSnd R q f).hom :=
  (relativeConvolutionRestriction_original_isPullback R q f).isoPullback_hom_snd

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
