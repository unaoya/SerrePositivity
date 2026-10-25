module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingNaturality

/-!
概要：元の全単体 Hom 同値の転置は、制限と標的射の両方に自然。
方針：元の curry の自然性と同じ同値の両逆を使う。
規約：任意の小さい単体集合・元の全射を保持する。
使われ方：実相対 AW 制限の可換平方を、元の単体的持ち上げ平方から回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} {K L : SSet.{0}}

lemma smallMultiplicativeMappingTranspose_precompose
    (a : SSet.uliftFunctor.{u, 0}.obj L ⟶ multiplicativeMappingSimplices R A B) (g : K ⟶ L) :
    smallMultiplicativeMappingTranspose R (SSet.uliftFunctor.{u, 0}.map g ≫ a) =
      smallMultiplicativeMappingTranspose R a ≫ (simplicialConvolution R B).map g.op := by
  apply (smallMultiplicativeMappingEquiv R).injective
  change smallMultiplicativeMappingCurry R _ = smallMultiplicativeMappingCurry R _
  rw [← smallMultiplicativeMappingCurry_precompose,
    smallMultiplicativeMappingCurry_transpose, smallMultiplicativeMappingCurry_transpose]

lemma smallMultiplicativeMappingTranspose_postcompose
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ multiplicativeMappingSimplices R A B) (q : B ⟶ C) :
    smallMultiplicativeMappingTranspose R (a ≫ multiplicativeMappingPostcompose R A q) =
      smallMultiplicativeMappingTranspose R a ≫
        (simplicialConvolutionTargetNatTrans R q).app (op K) := by
  apply (smallMultiplicativeMappingEquiv R).injective
  change smallMultiplicativeMappingCurry R _ = smallMultiplicativeMappingCurry R _
  rw [← smallMultiplicativeMappingCurry_postcompose,
    smallMultiplicativeMappingCurry_transpose, smallMultiplicativeMappingCurry_transpose]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
