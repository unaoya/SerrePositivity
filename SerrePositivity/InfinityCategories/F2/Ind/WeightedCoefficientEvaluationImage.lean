module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientEvaluationRestriction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoherentMapRealizationNormalizedRestriction

/-!
概要：元の共同密度変換を係数・始点に制限した実際の unstraightening の像を比較する。
方針：c1 の底変換自然性を、厳密に回収した元の評価図式と定値標的に適用する。
規約：元の変換頂点と元の実現射を保持。使われ方：指定余錐の実際の評価値写像への接続。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "H" => twistedElementsHomDiagram (weightedDensityProjection F)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "D" => weightedCoefficientEvaluationDiagram F i x
local notation "z" => weightedCoefficientEvaluationVertex F i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 元の c1 の指定変換頂点を、同じ係数・始点で制限した指定頂点。 -/
def weightedCoefficientEvaluationTransformationVertex :=
  (normalizedLeftTransformationRestriction H G k D (SSet.const z)
    (weightedCoefficientEvaluationBase_source F i x)
    (weightedCoefficientEvaluationBase_target F i x)).app (Opposite.op ⦋0⦌)
      ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (weightedDensityTransformation F).realization.transformation))

/-- 評価後の同じ定値標的を、元の共同標的へ戻す相対写像。 -/
def weightedCoefficientEvaluationRelativeTargetMap :=
  relativeFunctorSquarePost (leftUnstraighteningProjection (SSet.const z :
      (SSet.uliftFunctor.{u + 1, u}).obj (F.obj i).val.left ⟶ SpaceInfinity.{u}))
    (leftUnstraighteningProjection G) k
    (leftUnstraighteningMap (SSet.const z) G k (weightedCoefficientEvaluationBase_target F i x))
    (leftUnstraighteningMap_projection (SSet.const z) G k
      (weightedCoefficientEvaluationBase_target F i x)) (leftUnstraighteningProjection D)

/-- 同じ評価変換の実際の像は、元の共同実現射の同じ底上の制限と相対的に同型。 -/
def weightedCoefficientEvaluationRelativeImageIso :
    VertexIso ((leftUnstraighteningMappingSpaceMap D (SSet.const z) ≫
      weightedCoefficientEvaluationRelativeTargetMap F i x).app (Opposite.op ⦋0⦌)
        (weightedCoefficientEvaluationTransformationVertex F i x))
      ((relativeFunctorOverPre (leftUnstraighteningProjection G)
        (Over.homMk (leftUnstraighteningMap D H k (weightedCoefficientEvaluationBase_source F i x))
          (leftUnstraighteningMap_projection D H k
            (weightedCoefficientEvaluationBase_source F i x)) :
          Over.mk (leftUnstraighteningProjection D ≫ k) ⟶
            Over.mk (leftUnstraighteningProjection H))).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection H)
          (coherentRealizationLargeMap H G (weightedDensityTransformation F).map)
          (coherentRealizationLargeMap_projection H G (weightedDensityTransformation F).map
            (weightedDensityTransformation F).over_base))) :=
  coherentMapRealizationNormalizedRestrictionIso H G (weightedDensityTransformation F).map
    (weightedDensityTransformation F).over_base (weightedDensityTransformation F).realization
    k D (SSet.const z) (weightedCoefficientEvaluationBase_source F i x)
    (weightedCoefficientEvaluationBase_target F i x)

end SerrePositivity.InfinityCategories.F2.Ind
