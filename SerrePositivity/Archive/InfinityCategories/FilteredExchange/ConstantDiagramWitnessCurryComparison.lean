module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramWitnessEndpointComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorCurryPostValue
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTargetVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionCurryComparison

/-!
概要：元の二実証拠の相対 curry 比較を、同じ二実輸送の指定比較の curry へ移す。
方針：定値 fiber の厳密な curry 公式と同じ endpointIso の値の同定を合成する。
規約：元の両実射と指定比較を保持。使われ方：下側三角形因子の消去。
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
/-- 元の指定 curry 比較の定値 fiber 像は、同じ二実輸送の指定比較の通常の curry。 -/
lemma constantDiagramWitnessCurryComparison_heq_transport
    (g₀ g₁ : E ⊗ K ⟶ leftUnstraightening (SSet.const y : B ⟶ SpaceInfinity))
    (hg₀ : g₀ ≫ leftUnstraighteningProjection (SSet.const y) = fst E K ≫ q)
    (hg₁ : g₁ ≫ leftUnstraighteningProjection (SSet.const y) = fst E K ≫ q)
    (w₀ : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y) t g₀)
    (w₁ : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y) t g₁)
    (hv : v ≫ pointedSpaceProjection = i ≫ d)
    (hj : j ≫ d = (fst E K ≫ q) ≫ (SSet.const y : B ⟶ SpaceInfinity)) :
    HEq ((relativeFunctorExtensionEndpoint_curryIso pointedSpaceProjection d i hi v hv
      j (SSet.const y) q hj w₀.prism w₁.prism w₀.projection w₁.projection
      w₀.source w₁.source g₀ g₁ hg₀ hg₁ w₀.target w₁.target).postcomp
        (constantUnstraighteningRelativeIso q y).hom)
      (VertexIso.map ((constantDiagramTransportWitness w₀).endpointIso pointedSpaceProjection
        (constantUnstraighteningFiberProjection B x) (intervalMappingUncurry a)
        (intervalMappingUncurry_one a) (constantDiagramTransportWitness w₁))
        (functorSpaceCurryMap E K (vertexFiber pointedSpaceProjection y))) := by
  let η := relativeFunctorExtensionEndpoint_witnessIso pointedSpaceProjection
    d i hi v hv j (SSet.const y) (fst E K ≫ q) hj w₀.prism w₁.prism
    w₀.projection w₁.projection w₀.source w₁.source g₀ g₁ hg₀ hg₁ w₀.target w₁.target
  refine (relativeFunctorCurryIso_constant_fiber q y g₀ g₁ hg₀ hg₁ η).trans ?_
  have hs := (constantUnstraighteningRelativeIso_vertex (fst E K ≫ q) y g₀ hg₀).trans
    (congrArg functorVertex (constantDiagramTransportWitness_endpoint w₀).symm)
  have ht := (constantUnstraighteningRelativeIso_vertex (fst E K ≫ q) y g₁ hg₁).trans
    (congrArg functorVertex (constantDiagramTransportWitness_endpoint w₁).symm)
  exact vertexIso_map_heq_of_heq _ _ hs ht
    (constantDiagramWitnessEndpointComparison_heq_transport a g₀ g₁ hg₀ hg₁ w₀ w₁ hv hj)
    (functorSpaceCurryMap E K (vertexFiber pointedSpaceProjection y))

end SerrePositivity.InfinityCategories.F2
