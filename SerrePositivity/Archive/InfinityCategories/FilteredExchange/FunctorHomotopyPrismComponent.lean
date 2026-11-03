module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismComponentSource
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyExtensionSource

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

/-- 元の初期値固定の二証拠の指定比較を、同じ全 prism 空間へ写した値。 -/
def functorHomotopyExtensionComparison :=
  VertexIso.map ((hc).vertexIso ((z).point hv) (w.point hv)) r

/-- 全 prism 比較の実証拠での成分は、元の同じ初期値固定の指定比較そのもの。 -/
lemma functorHomotopyPrismSectionComparison_heq_extension :
    HEq ((functorHomotopyPrismSectionComparison H p).app x)
      (functorHomotopyExtensionComparison H p s hi w) := by
  have := functorHomotopyPrismSourceEvaluation_trivialKanFibration H p
  have ha : (q ≫ functorHomotopyPrismSection H p).app _ x =
      (r).app _ ((z).point hv) := by
    change (functorHomotopyPrismSection H p).app _ ((q).app _ x) = _
    rw [functorHomotopyPrismSourceEvaluation_vertex H p s hi w,
      functorHomotopyPrismSection_vertex H p s hi]
    rfl
  apply vertexIso_map_reflects_heq q (isFullyFaithful_of_trivialKanFibration q) _ _ ha rfl
  exact (functorHomotopyPrismSectionComparison_witness_source H p s hi w).trans
    (functorHomotopyExtension_comparison_source H p s hi w
      ((hc).vertexIso ((z).point hv) (w.point hv))).symm

end SerrePositivity.InfinityCategories.F2
