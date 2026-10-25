module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeConvolutionRestriction
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeSmallMappingNaturality

/-!
概要：元の相対小単体写像から実制限標的への境界射を作り、指定 lift を戻す。
方針：固定底の式で元の pullback へ入り、二射影で全制限と底を回収する。
規約：lift の存在はここでは仮定済み成果にせず、与えられた実射のみを輸送する。
使われ方：実相対 AW 制限の全射擬同型性からのホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A X B : Mon (Complex R)}
  (q : X ⟶ B) (s : A ⟶ B) {K L : SSet.{0}} (f : K ⟶ L)

lemma relativeSmallMappingTranspose_injective :
    Function.Injective (relativeSmallMappingTranspose R q s (K := K)) := by
  intro a b h
  apply (relativeSmallMappingEquiv R q s).symm.injective
  exact Subtype.ext h

def relativeSmallMappingBoundary
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s) :
    A ⟶ relativeConvolutionRestrictionTarget R q f :=
  pullback.lift (relativeSmallMappingTranspose R q s a)
    (s ≫ (simplicialConvolutionConstant R B).app (op L)) (by
      rw [relativeSmallMappingTranspose_over, Category.assoc]
      have h := (simplicialConvolutionConstant R B).naturality f.op
      change 𝟙 B ≫ (simplicialConvolutionConstant R B).app (op K) =
        (simplicialConvolutionConstant R B).app (op L) ≫ (simplicialConvolution R B).map f.op at h
      rw [Category.id_comp] at h
      exact congrArg (fun t => s ≫ t) h)

lemma relativeSmallMappingBoundary_fst
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s) :
    relativeSmallMappingBoundary R q s f a ≫ relativeConvolutionRestrictionFst R q f =
      relativeSmallMappingTranspose R q s a := pullback.lift_fst _ _ _

lemma relativeSmallMappingBoundary_snd
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s) :
    relativeSmallMappingBoundary R q s f a ≫ relativeConvolutionRestrictionSnd R q f =
      s ≫ (simplicialConvolutionConstant R B).app (op L) := pullback.lift_snd _ _ _

variable (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s)
  (b : A ⟶ (simplicialConvolution R X).obj (op L))
  (hb : b ≫ relativeConvolutionRestriction R q f = relativeSmallMappingBoundary R q s f a)

include hb

lemma relativeSmallMappingLift_restriction :
    b ≫ (simplicialConvolution R X).map f.op = relativeSmallMappingTranspose R q s a := by
  have h := congrArg (fun t => t ≫ relativeConvolutionRestrictionFst R q f) hb
  simpa only [Category.assoc, relativeConvolutionRestriction_fst,
    relativeSmallMappingBoundary_fst] using h

lemma relativeSmallMappingLift_over :
    b ≫ (simplicialConvolutionTargetNatTrans R q).app (op L) =
      s ≫ (simplicialConvolutionConstant R B).app (op L) := by
  have h := congrArg (fun t => t ≫ relativeConvolutionRestrictionSnd R q f) hb
  simpa only [Category.assoc, relativeConvolutionRestriction_snd,
    relativeSmallMappingBoundary_snd] using h

def relativeSmallMappingLift :
    SSet.uliftFunctor.{u, 0}.obj L ⟶ relativeMultiplicativeMappingSimplices R q s :=
  relativeSmallMappingCurry R q s b (relativeSmallMappingLift_over R q s f a b hb)

lemma relativeSmallMappingLift_extension :
    SSet.uliftFunctor.{u, 0}.map f ≫ relativeSmallMappingLift R q s f a b hb = a := by
  apply relativeSmallMappingTranspose_injective R q s
  rw [relativeSmallMappingTranspose_precompose, relativeSmallMappingLift,
    relativeSmallMappingTranspose_curry, relativeSmallMappingLift_restriction R q s f a b hb]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
