module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeSmallMappingEquiv

/-!
概要：固定底の実 Hom 同値は全ての小さい単体集合の制限と可換。
方針：元の標的射・定数射の自然性と相対 pullback の両射影で照合する。
規約：底射 s を変えず、元の制限射をそのまま使う。
使われ方：相対ホーンの実代数的充填を元の単体的充填へ戻す。
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
  (q : X ⟶ B) (s : A ⟶ B) {K L : SSet.{0}} (g : K ⟶ L)

lemma relativeSmallMappingRestriction_over
    (f : A ⟶ (simplicialConvolution R X).obj (op L))
    (hf : f ≫ (simplicialConvolutionTargetNatTrans R q).app (op L) =
      s ≫ (simplicialConvolutionConstant R B).app (op L)) :
    (f ≫ (simplicialConvolution R X).map g.op) ≫
        (simplicialConvolutionTargetNatTrans R q).app (op K) =
      s ≫ (simplicialConvolutionConstant R B).app (op K) := by
  rw [Category.assoc, (simplicialConvolutionTargetNatTrans R q).naturality,
    ← Category.assoc, hf, Category.assoc]
  have h := (simplicialConvolutionConstant R B).naturality g.op
  change 𝟙 B ≫ (simplicialConvolutionConstant R B).app (op K) =
    (simplicialConvolutionConstant R B).app (op L) ≫ (simplicialConvolution R B).map g.op at h
  rw [Category.id_comp] at h
  exact congrArg (fun t => s ≫ t) h.symm

lemma relativeSmallMappingCurry_precompose
    (f : A ⟶ (simplicialConvolution R X).obj (op L))
    (hf : f ≫ (simplicialConvolutionTargetNatTrans R q).app (op L) =
      s ≫ (simplicialConvolutionConstant R B).app (op L)) :
    SSet.uliftFunctor.{u, 0}.map g ≫ relativeSmallMappingCurry R q s f hf =
      relativeSmallMappingCurry R q s (f ≫ (simplicialConvolution R X).map g.op)
        (relativeSmallMappingRestriction_over R q s g f hf) := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ relativeMultiplicativeMappingProjection R q s =
      _ ≫ relativeMultiplicativeMappingProjection R q s
    rw [Category.assoc, relativeSmallMappingCurry_projection,
      relativeSmallMappingCurry_projection, smallMultiplicativeMappingCurry_precompose]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

lemma relativeSmallMappingTranspose_precompose
    (a : SSet.uliftFunctor.{u, 0}.obj L ⟶ relativeMultiplicativeMappingSimplices R q s) :
    relativeSmallMappingTranspose R q s (SSet.uliftFunctor.{u, 0}.map g ≫ a) =
      relativeSmallMappingTranspose R q s a ≫ (simplicialConvolution R X).map g.op := by
  apply (smallMultiplicativeMappingEquiv R).injective
  change smallMultiplicativeMappingCurry R _ = smallMultiplicativeMappingCurry R _
  rw [← smallMultiplicativeMappingCurry_precompose, relativeSmallMappingTranspose,
    relativeSmallMappingTranspose, smallMultiplicativeMappingCurry_transpose,
    smallMultiplicativeMappingCurry_transpose, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
