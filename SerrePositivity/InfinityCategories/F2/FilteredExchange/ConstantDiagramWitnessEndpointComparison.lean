module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTransportRightPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionConstantComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberEndpointDataEquality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberTransportFamilyRightComparisonEquality

/-!
概要：元の定値図式の二実証拠の指定比較を、同じ二輸送の endpointIso へ戻す。
方針：定値 fiber 表示の後、底・始点・実 prism・実終点を厳密に照合する。
規約：元の指定比較を保持。使われ方：元の三角形の下側輸送因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : K ⟶ intervalMappingSpace x y)
local notation "E" => leftUnstraightening (SSet.const x : B ⟶ SpaceInfinity)
local notation "q" => leftUnstraighteningProjection (SSet.const x : B ⟶ SpaceInfinity)
local notation "t" => constantDiagramTransformation B a
local notation "d" => ((Δ[1] ◁ q) ▷ K) ≫ functorParameterizedPrism (intervalMappingUncurry t)
local notation "i" => prismEndpoint 0 E ▷ K
local notation "j" => prismEndpoint 1 E ▷ K
local notation "hi" => leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K
local notation "v" => fst E K ≫ pullback.fst pointedSpaceProjection (SSet.const x : B ⟶ _)
local notation "P" => constantUnstraighteningFiberProjection B y

/-- 二つの元の実証拠の指定比較の fiber 像は、同じ二実輸送の endpointIso。 -/
lemma constantDiagramWitnessEndpointComparison_heq_transport
    (g₀ g₁ : E ⊗ K ⟶ leftUnstraightening (SSet.const y : B ⟶ SpaceInfinity))
    (hg₀ : g₀ ≫ leftUnstraighteningProjection (SSet.const y) = fst E K ≫ q)
    (hg₁ : g₁ ≫ leftUnstraighteningProjection (SSet.const y) = fst E K ≫ q)
    (w₀ : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y) t g₀)
    (w₁ : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y) t g₁)
    (hv : v ≫ pointedSpaceProjection = i ≫ d)
    (hj : j ≫ d = (fst E K ≫ q) ≫ (SSet.const y : B ⟶ SpaceInfinity)) :
    HEq (VertexIso.map
      (relativeFunctorExtensionEndpoint_witnessIso pointedSpaceProjection d i hi v hv
        j (SSet.const y) (fst E K ≫ q) hj w₀.prism w₁.prism w₀.projection w₁.projection
        w₀.source w₁.source g₀ g₁ hg₀ hg₁ w₀.target w₁.target)
      (constantUnstraighteningRelativeIso (fst E K ≫ q) y).hom)
      ((constantDiagramTransportWitness w₀).endpointIso pointedSpaceProjection
        (constantUnstraighteningFiberProjection B x) (intervalMappingUncurry a)
        (intervalMappingUncurry_one a) (constantDiagramTransportWitness w₁)) := by
  refine (relativeExtensionConstantEndpoint_witnessIso_heq_fiber d i hi v hv j
    (fst E K ≫ q) y hj w₀.prism w₁.prism w₀.projection w₁.projection
    w₀.source w₁.source g₀ g₁ hg₀ hg₁ w₀.target w₁.target).trans ?_
  let T := constantDiagramTransportWitness w₀
  let U := constantDiagramTransportWitness w₁
  refine (relativeExtensionFiberEndpoint_witnessIso_heq_of_dataEq pointedSpaceProjection
    d (fiberTransportFamilyRightBase E (intervalMappingUncurry a)) i hi
    v (fst E K ≫ constantUnstraighteningFiberProjection B x ≫
      vertexFiberι pointedSpaceProjection x) hv
    (fiberTransportFamilyRightComparison_initial _ _ _ T) j y
    (hj.trans (SSet.comp_const _ y)) (fiberTransportFamilyRightComparison_final _
      (intervalMappingUncurry_one a))
    w₀.prism w₁.prism (fiberTransportFamilyRightPrism T) (fiberTransportFamilyRightPrism U)
    w₀.projection w₁.projection
    (fiberTransportFamilyRightPrism_projection T) (fiberTransportFamilyRightPrism_projection U)
    w₀.source w₁.source
    (fiberTransportFamilyRightPrism_source T) (fiberTransportFamilyRightPrism_source U)
    (g₀ ≫ P) (g₁ ≫ P) T.endpoint U.endpoint
    (by rw [Category.assoc, constantUnstraighteningFiberProjection_ι]; exact w₀.target)
    (by rw [Category.assoc, constantUnstraighteningFiberProjection_ι]; exact w₁.target)
    (fiberTransportFamilyRightPrism_target T) (fiberTransportFamilyRightPrism_target U)
    (constantDiagramTransportWitness_rightBase w₀)
    (by rw [constantUnstraighteningFiberProjection_ι])
    (constantDiagramTransportWitness_rightPrism w₀).symm
    (constantDiagramTransportWitness_rightPrism w₁).symm
    (constantDiagramTransportWitness_endpoint w₀).symm
    (constantDiagramTransportWitness_endpoint w₁).symm).trans ?_
  exact heq_of_eq (fiberTransportFamilyRightComparison_eq_endpointIso pointedSpaceProjection
    (constantUnstraighteningFiberProjection B x) (intervalMappingUncurry a)
    (intervalMappingUncurry_one a) T U)

end SerrePositivity.InfinityCategories.F2
