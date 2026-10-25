module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingNaturality

/-!
概要：指定底を保つ実乗法的写像の、小さい単体集合上の相対比較。
方針：全単体の比較の自然性と元の pullback の普遍性を使う。
規約：元の底射 s と元の標的射 q を厳密に保持する。
使われ方：cell 源上の相対ホーン充填と導来比較の固定底の前段。
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

def relativeSmallMappingTranspose
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s) :
    A ⟶ (simplicialConvolution R X).obj (op K) :=
  smallMultiplicativeMappingTranspose R (a ≫ relativeMultiplicativeMappingProjection R q s)

lemma relativeSmallMappingTranspose_over
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s) :
    relativeSmallMappingTranspose R q s a ≫
        (simplicialConvolutionTargetNatTrans R q).app (op K) =
      s ≫ (simplicialConvolutionConstant R B).app (op K) := by
  apply (smallMultiplicativeMappingEquiv R).injective
  change smallMultiplicativeMappingCurry R _ = smallMultiplicativeMappingCurry R _
  rw [← smallMultiplicativeMappingCurry_postcompose, smallMultiplicativeMappingCurry_constant,
    relativeSmallMappingTranspose, smallMultiplicativeMappingCurry_transpose,
    Category.assoc, relativeMultiplicativeMapping_condition, ← Category.assoc]
  exact congrArg (fun t => t ≫ multiplicativeMappingBase R s)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

variable (f : A ⟶ (simplicialConvolution R X).obj (op K))
  (hf : f ≫ (simplicialConvolutionTargetNatTrans R q).app (op K) =
    s ≫ (simplicialConvolutionConstant R B).app (op K))

def relativeSmallMappingCurry :
    SSet.uliftFunctor.{u, 0}.obj K ⟶ relativeMultiplicativeMappingSimplices R q s :=
  pullback.lift (smallMultiplicativeMappingCurry R f)
    (SSet.stdSimplex.isTerminalObj₀.from _) (by
      rw [smallMultiplicativeMappingCurry_postcompose, hf,
        smallMultiplicativeMappingCurry_constant])

lemma relativeSmallMappingCurry_projection :
    relativeSmallMappingCurry R q s f hf ≫ relativeMultiplicativeMappingProjection R q s =
      smallMultiplicativeMappingCurry R f :=
  pullback.lift_fst _ _ _

lemma relativeSmallMappingCurry_base :
    relativeSmallMappingCurry R q s f hf ≫ relativeMultiplicativeMappingBaseProjection R q s =
      SSet.stdSimplex.isTerminalObj₀.from _ :=
  pullback.lift_snd _ _ _

lemma relativeSmallMappingTranspose_curry :
    relativeSmallMappingTranspose R q s (relativeSmallMappingCurry R q s f hf) = f := by
  rw [relativeSmallMappingTranspose, relativeSmallMappingCurry_projection,
    smallMultiplicativeMappingTranspose_curry]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
