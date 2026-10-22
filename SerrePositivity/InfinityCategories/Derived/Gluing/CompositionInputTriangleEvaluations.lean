module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputDiagonals

/-! 入力 fiber 上の元の二合成三角形の評価と、固定辺・可変辺・対角の回収。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedFirstInputTriangleEvaluation (X Y : DGGluingObject R C D M) :=
  ((Δ[2] : SSet.{max (u + 1) v w}) ◁ pullback.fst
    (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (dgGluingDerivedRightCoefficientInput R C D M X Y)) ≫
    dgGluingFirstFixedCompositionEvaluation (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right)))

def dgGluingDerivedLastInputTriangleEvaluation (X Y : DGGluingObject R C D M) :=
  ((Δ[2] : SSet.{max (u + 1) v w}) ◁ pullback.fst
    (compositionCorrespondenceFirst
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)) ≫
    compositionCorrespondenceEvaluation
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y)

lemma dgGluingDerivedFirstInputTriangleEvaluation_fixed (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      fst _ _ ≫ SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M X).edge := by
  rw [dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingFirstFixedCompositionEvaluation_first,
    ← Category.assoc, whiskerLeft_fst]

lemma dgGluingDerivedLastInputTriangleEvaluation_fixed (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      fst _ _ ≫ SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  rw [dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, compositionCorrespondenceEvaluation_last,
    ← Category.assoc, whiskerLeft_fst]

lemma dgGluingDerivedFirstInputTriangleEvaluation_variable (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      intervalMappingUncurry (dgGluingDerivedFirstCompositionInputProjection R C D M X Y ≫
        dgGluingDerivedRightCoefficientInput R C D M X Y) := by
  rw [dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingFirstFixedCompositionEvaluation_last,
    ← intervalMappingUncurry_precomp]
  apply congrArg intervalMappingUncurry
  exact pullback.condition

lemma dgGluingDerivedLastInputTriangleEvaluation_variable (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      intervalMappingUncurry (dgGluingDerivedLastCompositionInputProjection R C D M X Y ≫
        dgGluingDerivedLeftCoefficientInput R C D M X Y) := by
  rw [dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, compositionCorrespondenceEvaluation_first,
    ← intervalMappingUncurry_precomp]
  apply congrArg intervalMappingUncurry
  exact pullback.condition

lemma dgGluingDerivedFirstInputTriangleEvaluation_diagonal (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      intervalMappingUncurry (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, ← dgGluingFirstFixedCompositionDiagonal_uncurry,
    ← intervalMappingUncurry_precomp]
  rfl

lemma dgGluingDerivedLastInputTriangleEvaluation_diagonal (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      intervalMappingUncurry (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, ← compositionCorrespondenceDiagonal_uncurry,
    ← intervalMappingUncurry_precomp]
  rfl

end SerrePositivity.InfinityCategories
