module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionUniversalInitial
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleVertexIsoNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMappingLaws

/-!
概要：元の初期値固定の全延長空間の比較は、動く始点評価では同じ指定始点の恒等となる。
方針：全延長族の初期式を相対端点評価へ渡し、定値写像による同型の像を計算する。
規約：元の指定同型を保持。使われ方：全自然な prism 比較と F1 の指定比較の同定。
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
local notation "E" =>
  relativeFunctorExtensionSpace pointedSpaceProjection d (prismEndpoint 0 C) v hv
local notation "r" =>
  relativeFunctorExtensionSpaceι pointedSpaceProjection d (prismEndpoint 0 C) v hv
local notation "q" => functorHomotopyPrismSourceEvaluation H p
local notation "b" => relativeFunctorVertex (leftUnstraighteningProjection F) p s hi

/-- 同じ全初期値を固定する延長族は、元の始域射の頂点へ定値に評価される。 -/
lemma functorHomotopyExtension_source_constant : r ≫ q = (SSet.const b : E ⟶ _) := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [functorHomotopyPrismSourceEvaluation, relativeFunctorRestrictedEndpoint_uncurry,
      relativeExtensionUniversal_initial]
    change (fst C E ≫ s ≫ pullback.fst pointedSpaceProjection F) =
      uncurry (SSet.const (functorVertex s)) ≫ pullback.fst pointedSpaceProjection F
    rw [uncurry_const_functorVertex, Category.assoc]
  · exact (relativeFunctorUncurry_projection _).trans (relativeFunctorUncurry_projection _).symm

/-- 元の fiber 内の指定比較は、始点評価で同じ元の始点頂点の恒等同型へ戻る。 -/
lemma functorHomotopyExtension_comparison_source {x y : E _⦋0⦌} (a : VertexIso x y) :
    HEq (VertexIso.map (VertexIso.map a r) q) (Iso.refl (SSet.HomotopyCategory.mk b)) := by
  have hE := relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection d
    (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C) v hv
  have := hE.kanComplex
  rw [VertexIso.map_comp]
  have hc := vertexIso_map_heq a (functorHomotopyExtension_source_constant H p s hi w)
  rw [VertexIso.map_const] at hc
  have hr {z₀ z₁ : hoFunctor.obj (relativeFunctorSpace (leftUnstraighteningProjection F) p)}
      (h : z₀ = z₁) : HEq (Iso.refl z₀) (Iso.refl z₁) := by
    cases h
    rfl
  exact hc.trans (hr (congrArg SSet.HomotopyCategory.mk (constMap_vertex_value b x)))

end SerrePositivity.InfinityCategories.F2
