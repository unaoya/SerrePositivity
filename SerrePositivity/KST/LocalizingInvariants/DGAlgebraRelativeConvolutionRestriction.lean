module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionLimits

/-!
概要：指定標的射を保つ実 AW 制限の相対標的と二つの射影。
方針：元の標的自然変換と単体制限の可換正方形から実代数の pullback を作る。
規約：元の q・包含 f と元の AW 畳み込みを保持する。
使われ方：固定底上のホーン充填で、代数射の持ち上げを行う実標的。
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

def relativeConvolutionRestrictionTarget : Mon (Complex R) :=
  pullback ((simplicialConvolutionTargetNatTrans R q).app (op K))
    ((simplicialConvolution R B).map f.op)

def relativeConvolutionRestriction :
    (simplicialConvolution R X).obj (op L) ⟶
      relativeConvolutionRestrictionTarget R q f :=
  pullback.lift ((simplicialConvolution R X).map f.op)
    ((simplicialConvolutionTargetNatTrans R q).app (op L))
    ((simplicialConvolutionTargetNatTrans R q).naturality f.op)

def relativeConvolutionRestrictionFst :
    relativeConvolutionRestrictionTarget R q f ⟶
      (simplicialConvolution R X).obj (op K) := pullback.fst _ _

def relativeConvolutionRestrictionSnd :
    relativeConvolutionRestrictionTarget R q f ⟶
      (simplicialConvolution R B).obj (op L) := pullback.snd _ _

@[reassoc]
lemma relativeConvolutionRestriction_fst :
    relativeConvolutionRestriction R q f ≫ relativeConvolutionRestrictionFst R q f =
      (simplicialConvolution R X).map f.op := pullback.lift_fst _ _ _

@[reassoc]
lemma relativeConvolutionRestriction_snd :
    relativeConvolutionRestriction R q f ≫ relativeConvolutionRestrictionSnd R q f =
      (simplicialConvolutionTargetNatTrans R q).app (op L) := pullback.lift_snd _ _ _

lemma relativeConvolutionRestriction_isPullback :
    IsPullback (relativeConvolutionRestrictionFst R q f)
      (relativeConvolutionRestrictionSnd R q f)
      ((simplicialConvolutionTargetNatTrans R q).app (op K))
      ((simplicialConvolution R B).map f.op) := IsPullback.of_hasPullback _ _

lemma relativeConvolutionRestriction_underlying_isPullback :
    IsPullback (relativeConvolutionRestrictionFst R q f).hom
      (relativeConvolutionRestrictionSnd R q f).hom
      ((simplicialConvolutionTargetNatTrans R q).app (op K)).hom
      ((simplicialConvolution R B).map f.op).hom :=
  (relativeConvolutionRestriction_isPullback R q f).map (Mon.forget (Complex R))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
