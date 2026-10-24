module
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputStrictForget
/-! # 正本の元二入力付き同一対角模型の厳密な座標同型

概要：同じ合成対角模型を元左右 Hom 入力の上で引き戻したものへ、入力付き模型を同定する。
方針：四座標を保持する一般の厳密同型を、正本の二つの合成対応へ実例化する。
規約：二入力を忘れず、元合成三角形・共通対角・全 Hom 入力を保持する。
使われ方：入力付き模型の実逆射を主比較の標的へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingCompositionInputStrictCoordinatesIso :=
  dgGluingRestrictedDiagonalInputIso
    (compositionCorrespondenceFirst
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (compositionCorrespondenceDiagonal
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)
    (dgGluingDerivedRightCoefficientInput R C D M X Y)


def dgGluingCompositionInputRawPair :=
  dgGluingRestrictedDiagonalInputPair
    (compositionCorrespondenceFirst
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (compositionCorrespondenceDiagonal
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)
    (dgGluingDerivedRightCoefficientInput R C D M X Y)


lemma dgGluingCompositionInputStrictCoordinatesIso_forget :
    (dgGluingCompositionInputStrictCoordinatesIso R C D M X Y).hom ≫ pullback.fst _ _ =
      dgGluingCompositionInputStrictForget R C D M X Y :=
  dgGluingRestrictedDiagonalInputIso_forget _ _ _ _ _ _

lemma dgGluingCompositionInputStrictCoordinatesIso_inputs :
    (dgGluingCompositionInputStrictCoordinatesIso R C D M X Y).hom ≫ pullback.snd _ _ =
      dgGluingCompositionInputRawPair R C D M X Y :=
  dgGluingRestrictedDiagonalInputIso_inputs _ _ _ _ _ _
end SerrePositivity.InfinityCategories
