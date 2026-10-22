module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeRestriction

/-!
概要：元の native 評価余錐の標準変換の実際の像を、元の共同実現射の制限へ比較する。
方針：同じ評価変換頂点の厳密な同定を、c1 の正規化した底変換自然性へ代入する。
規約：元の余錐・図式・頂点を保持。使われ方：実際の native 評価 fiber 写像の余極限判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "H" => twistedElementsHomDiagram (weightedDensityProjection F)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 元の native 評価余錐の標準変換は、元の指定係数変換の同じ評価像と同型。 -/
def weightedCoefficientNativeCoconeTransformationIso :
    VertexIso ((F2.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
      (F2.coconeMappingPointAt (weightedCoefficientNativeEvaluationCocone κ F hF i x) z
        (weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x)))
      (weightedCoefficientNativeEvaluatedTransformation κ F hF i x) :=
  weightedCoefficientCoconePostTransformationIso κ F hF i (indPresheafEvaluation κ x)

/-- 元の native 評価の定値標的を、同じ共同標的へ戻す相対写像。 -/
def weightedCoefficientNativeRelativeTargetMap :=
  relativeFunctorSquarePost (leftUnstraighteningProjection (SSet.const z :
      (SSet.uliftFunctor.{u + 1, u}).obj (F.obj i).val.left ⟶ SpaceInfinity.{u}))
    (leftUnstraighteningProjection G) k
    (leftUnstraighteningMap (SSet.const z) G k
      (weightedCoefficientNativeEvaluationBase_target κ F hF i x))
    (leftUnstraighteningMap_projection (SSet.const z) G k
      (weightedCoefficientNativeEvaluationBase_target κ F hF i x)) (leftUnstraighteningProjection D)

/-- 元の共同実現射の同じ制限を、元の native 評価図式の相対写像空間の頂点で読む。 -/
def weightedCoefficientNativeRelativeRealizationVertex :=
  (relativeFunctorOverPre (leftUnstraighteningProjection G)
    (Over.homMk (leftUnstraighteningMap D H k
      (weightedCoefficientNativeEvaluationBase_source κ F i x))
      (leftUnstraighteningMap_projection D H k
        (weightedCoefficientNativeEvaluationBase_source κ F i x)) :
      Over.mk (leftUnstraighteningProjection D ≫ k) ⟶
        Over.mk (leftUnstraighteningProjection H))).app
        (Opposite.op ⦋0⦌)
    (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection H)
      (coherentRealizationLargeMap H G (weightedDensityTransformation F).map)
      (coherentRealizationLargeMap_projection H G (weightedDensityTransformation F).map
        (weightedDensityTransformation F).over_base))

/-- 元の native 評価変換の実際の像は、元の共同実現射の同じ制限と相対的に同型。 -/
def weightedCoefficientNativeEvaluationRelativeImageIso :
    VertexIso ((leftUnstraighteningMappingSpaceMap D (SSet.const z) ≫
      weightedCoefficientNativeRelativeTargetMap κ F hF i x).app (Opposite.op ⦋0⦌)
        (weightedCoefficientNativeEvaluatedTransformation κ F hF i x))
      (weightedCoefficientNativeRelativeRealizationVertex κ F i x) := by
  have he := coherentMapRealizationNormalizedRestrictionIso H G
    (weightedDensityTransformation F).map
    (weightedDensityTransformation F).over_base (weightedDensityTransformation F).realization
    k D (SSet.const z) (weightedCoefficientNativeEvaluationBase_source κ F i x)
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)
  change VertexIso ((leftUnstraighteningMappingSpaceMap D (SSet.const z) ≫
    weightedCoefficientNativeRelativeTargetMap κ F hF i x).app (Opposite.op ⦋0⦌)
      ((weightedCoefficientNativeJointRestriction κ F hF i x).app (Opposite.op ⦋0⦌)
        ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
          (ULift.up (weightedDensityTransformation F).realization.transformation)))) _ at he
  rw [weightedCoefficientNativeJointRestriction_vertex] at he
  exact he

/-- 同じ native 評価余錐の標準変換の像も、元の共同実現射の同じ制限と相対的に同型。 -/
def weightedCoefficientNativeCoconeRelativeImageIso :
    VertexIso ((leftUnstraighteningMappingSpaceMap D (SSet.const z) ≫
      weightedCoefficientNativeRelativeTargetMap κ F hF i x).app (Opposite.op ⦋0⦌)
      ((F2.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
        (F2.coconeMappingPointAt (weightedCoefficientNativeEvaluationCocone κ F hF i x) z
          (weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x))))
      (weightedCoefficientNativeRelativeRealizationVertex κ F i x) :=
  (weightedCoefficientNativeCoconeTransformationIso κ F hF i x).map
    (leftUnstraighteningMappingSpaceMap D (SSet.const z) ≫
      weightedCoefficientNativeRelativeTargetMap κ F hF i x) ≪≫
    weightedCoefficientNativeEvaluationRelativeImageIso κ F hF i x

end SerrePositivity.InfinityCategories.F2.Ind
