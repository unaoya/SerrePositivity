module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeSmallMapping

/-!
概要：指定底を保つ実 AW 制限射と相対乗法的単体写像の同値。
方針：元の pullback の両射影と全単体比較の両逆で検証する。
規約：元の q と s の厳密な式を保持し、導来比較とは区別する。
使われ方：cell 源の相対ホーン充填の実入力と出力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A X B : Mon (Complex R)} {K : SSet.{0}}
  (q : X ⟶ B) (s : A ⟶ B)

lemma relativeSmallMappingCurry_transpose
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s) :
    relativeSmallMappingCurry R q s (relativeSmallMappingTranspose R q s a)
      (relativeSmallMappingTranspose_over R q s a) = a := by
  apply pullback.hom_ext
  · change _ ≫ relativeMultiplicativeMappingProjection R q s =
      a ≫ relativeMultiplicativeMappingProjection R q s
    rw [relativeSmallMappingCurry_projection, relativeSmallMappingTranspose,
      smallMultiplicativeMappingCurry_transpose]
  · change _ ≫ relativeMultiplicativeMappingBaseProjection R q s =
      a ≫ relativeMultiplicativeMappingBaseProjection R q s
    rw [relativeSmallMappingCurry_base]
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

def relativeSmallMappingEquiv :
    {f : A ⟶ (simplicialConvolution R X).obj (op K) //
      f ≫ (simplicialConvolutionTargetNatTrans R q).app (op K) =
        s ≫ (simplicialConvolutionConstant R B).app (op K)} ≃
      (SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s) where
  toFun f := relativeSmallMappingCurry R q s f.val f.property
  invFun a := ⟨relativeSmallMappingTranspose R q s a, relativeSmallMappingTranspose_over R q s a⟩
  left_inv f := by
    apply Subtype.ext
    exact relativeSmallMappingTranspose_curry R q s f.val f.property
  right_inv := relativeSmallMappingCurry_transpose R q s

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
