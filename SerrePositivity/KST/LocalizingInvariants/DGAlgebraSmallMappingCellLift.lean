module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeConvolutionRestriction
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingTransposeNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionArbitraryLift

/-!
概要：実相対 AW 制限の全射擬同型性を、cell 写像の全単体の持ち上げへ戻す。
方針：元の可換平方を全小単体の転置で pullback に移し、実 cell lift の両射影を回収する。
規約：二つの境界写像を全単体で保持する。制限射の性質は同じ実射について用いる。
使われ方：実ホーンおよび境界の証拠を適用する共通の代数的輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) {X B : Mon (Complex R)} (q : X ⟶ B)

lemma multiplicativeCellMapping_small_lift {K L : SSet.{0}} (f : K ⟶ L)
    (hs : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R (relativeConvolutionRestriction R q f).hom)
    (hw : QuasiIso (relativeConvolutionRestriction R q f).hom)
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶
      multiplicativeMappingSimplices R (cellResolution R A) X)
    (b : SSet.uliftFunctor.{u, 0}.obj L ⟶
      multiplicativeMappingSimplices R (cellResolution R A) B)
    (hab : a ≫ multiplicativeMappingPostcompose R (cellResolution R A) q =
      SSet.uliftFunctor.{u, 0}.map f ≫ b) :
    ∃ c : SSet.uliftFunctor.{u, 0}.obj L ⟶
        multiplicativeMappingSimplices R (cellResolution R A) X,
      SSet.uliftFunctor.{u, 0}.map f ≫ c = a ∧
        c ≫ multiplicativeMappingPostcompose R (cellResolution R A) q = b := by
  let a' := smallMultiplicativeMappingTranspose R a
  let b' := smallMultiplicativeMappingTranspose R b
  have hd : a' ≫ (simplicialConvolutionTargetNatTrans R q).app (op K) =
      b' ≫ (simplicialConvolution R B).map f.op := by
    have h := congrArg (smallMultiplicativeMappingTranspose R) hab
    rw [smallMultiplicativeMappingTranspose_postcompose,
      smallMultiplicativeMappingTranspose_precompose] at h
    exact h
  let d : cellResolution R A ⟶ relativeConvolutionRestrictionTarget R q f :=
    pullback.lift a' b' hd
  obtain ⟨c, hc⟩ := exists_cellResolutionArbitraryLift R
    (relativeConvolutionRestriction R q f) hs hw d
  have ha : c ≫ (simplicialConvolution R X).map f.op = a' := by
    calc
      _ = (c ≫ relativeConvolutionRestriction R q f) ≫
          relativeConvolutionRestrictionFst R q f := by
        rw [Category.assoc, relativeConvolutionRestriction_fst]
      _ = d ≫ relativeConvolutionRestrictionFst R q f :=
        congrArg (fun t => t ≫ relativeConvolutionRestrictionFst R q f) hc
      _ = a' := pullback.lift_fst _ _ _
  have hb : c ≫ (simplicialConvolutionTargetNatTrans R q).app (op L) = b' := by
    calc
      _ = (c ≫ relativeConvolutionRestriction R q f) ≫
          relativeConvolutionRestrictionSnd R q f := by
        rw [Category.assoc, relativeConvolutionRestriction_snd]
      _ = d ≫ relativeConvolutionRestrictionSnd R q f :=
        congrArg (fun t => t ≫ relativeConvolutionRestrictionSnd R q f) hc
      _ = b' := pullback.lift_snd _ _ _
  refine ⟨smallMultiplicativeMappingCurry R c, ?_, ?_⟩
  · rw [smallMultiplicativeMappingCurry_precompose, ha,
      smallMultiplicativeMappingCurry_transpose]
  · rw [smallMultiplicativeMappingCurry_postcompose, hb,
      smallMultiplicativeMappingCurry_transpose]


end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
