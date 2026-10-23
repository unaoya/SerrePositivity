module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoherentMapRealizationNormalizedRestriction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityJointRestriction

/-!
概要：密度評価変換の実際の unstraightening の像を、元の実現射の制限へ比較する。
方針：同じ c1 の変換頂点への制限作用と、両端を正規化した底変換自然性を組み合わせる。
規約：元の評価図式と定値標的を保持し、相対 Hom の中で比較する。
使われ方：native な密度 fiber 写像を元の大域評価へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "Dx" => presheafDensityEvaluationDiagram F x
local notation "z" => presheafDensityEvaluationVertex F x

/-- 評価後の定値標的の全空間を、元の全標的へ戻す相対 Hom の射。 -/
def presheafDensityEvaluationRelativeTargetMap :=
  relativeFunctorSquarePost (leftUnstraighteningProjection (SSet.const z))
    (leftUnstraighteningProjection G)
    ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
    (leftUnstraighteningMap (SSet.const z) G
      ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
      (presheafDensitySourceInclusion_target F x))
    (leftUnstraighteningMap_projection (SSet.const z) G
      ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
      (presheafDensitySourceInclusion_target F x)) (leftUnstraighteningProjection Dx)

/-- 評価図式の元の全空間への比較に沿う、元の相対 Hom の前合成。 -/
def presheafDensityEvaluationRelativeSourceMap :=
  relativeFunctorOverPre (leftUnstraighteningProjection G)
    (Over.homMk (leftUnstraighteningMap Dx H
      ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
      (presheafDensitySourceInclusion_source F x))
      (leftUnstraighteningMap_projection Dx H
        ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
        (presheafDensitySourceInclusion_source F x)) :
      Over.mk (leftUnstraighteningProjection Dx ≫
        (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x)) ⟶
          Over.mk (leftUnstraighteningProjection H))

/-- 同じ評価変換の実際の像は、同じ大域実現射の制限と相対的に同型。 -/
def presheafDensityEvaluationRelativeImageIso :
    VertexIso
      ((leftUnstraighteningMappingSpaceMap Dx (SSet.const z) ≫
        presheafDensityEvaluationRelativeTargetMap F x).app (Opposite.op ⦋0⦌)
          (presheafDensityEvaluatedTransformationVertex F x))
      ((presheafDensityEvaluationRelativeSourceMap F x).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection H)
          (coherentRealizationLargeMap H G (presheafDensityTransformation F).map)
          (coherentRealizationLargeMap_projection H G (presheafDensityTransformation F).map
            (presheafDensityTransformation F).over))) := by
  have he := coherentMapRealizationNormalizedRestrictionIso H G
    (presheafDensityTransformation F).map (presheafDensityTransformation F).over
    (presheafDensityTransformation F).realization
    ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x)) Dx (SSet.const z)
    (presheafDensitySourceInclusion_source F x) (presheafDensitySourceInclusion_target F x)
  change VertexIso
    ((leftUnstraighteningMappingSpaceMap Dx (SSet.const z) ≫
      presheafDensityEvaluationRelativeTargetMap F x).app (Opposite.op ⦋0⦌)
        ((presheafDensityJointRestriction F x).app (Opposite.op ⦋0⦌)
          ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
            (ULift.up (presheafDensityTransformation F).realization.transformation)))) _ at he
  rw [presheafDensityJointRestriction_vertex] at he
  exact he

end SerrePositivity.InfinityCategories.F2.Ind
