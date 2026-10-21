module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyPrismComponent
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionWitnessComparison

/-!
概要：始点も動く全 prism 比較の各点成分を、元の初期値固定の指定比較へ値まで同定する。
方針：始点射影の像が同じ恒等同型となることを、充満忠実性で反映する。
規約：元の実証拠・同型を保持。使われ方：F1 の指定始域比較へ全自然性を移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)
local notation "v" => s ≫ pullback.fst pointedSpaceProjection F
local notation "hv" => RelativeExtensionEndpointWitness.initial_base w
local notation "r" =>
  relativeFunctorExtensionSpaceι pointedSpaceProjection d (prismEndpoint 0 C) v hv
local notation "q" => functorHomotopyPrismSourceEvaluation H p
local notation "z" => functorHomotopySourceCanonicalWitness H p s hi
local notation "x" => relativeFunctorVertex pointedSpaceProjection d
  (RelativeExtensionEndpointWitness.extension w) (RelativeExtensionEndpointWitness.over w)
local notation "hc" => relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection d
  (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C) v hv

/-- 元の指定始域比較は、同じ初期値固定の全 prism 比較の終点像そのもの。 -/
lemma functorHomotopySourceEndpointIso_heq_extension :
    HEq (functorHomotopySourceEndpointIso H p s hi w)
      (VertexIso.map (functorHomotopyExtensionComparison H p s hi w)
        (functorHomotopyPrismTargetEvaluation H p)) := by
  have := (hc).kanComplex
  rw [functorHomotopyExtensionComparison, vertexIso_map_comp]
  exact relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection d
    (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C) v hv
    (prismEndpoint 1 C) G p w.endpoint_base (z).extension w.extension (z).over w.over
    (z).initial w.initial (z).endpoint w.endpoint (z).endpoint_over w.endpoint_over
    (z).evaluate w.evaluate

end SerrePositivity.InfinityCategories.F2
