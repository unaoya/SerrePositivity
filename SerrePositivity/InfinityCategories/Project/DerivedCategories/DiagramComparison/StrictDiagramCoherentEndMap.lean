module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramSourceFramePinched
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.FunctorPinchedEndMap

/-!
概要：元の実 source frame の全 Hom 単体から、元の評価図式の end 切断への射を構成する。
方針：同じ frame 比較、指定実評価、元の全関手同型の成分、固定した end 比較を合成する。
規約：全高次単体を持つ射を返す。同値性は RR02 に残し、追加の普遍性を仮定しない。
使われ方：3b-3 RR01、HTT 4.2.4.4 の実評価の充満忠実性への比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheYonedaEmbedding.Cocompletion
open Project.HomotopyDiagramComparison
open HA.DerivedCategoryModels.DerivedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance coherentEndSourceKan (X Y : StrictComplexDiagram A d) :
    KanComplex (strictDiagramFrameMapping A d X Y) :=
  strictDiagramFrameMapping_kanComplex A d X Y

/-- 元の strict 図式評価の同じ頂点が表す coherent 図式。 -/
def strictDiagramEvaluatedDiagram (X : StrictComplexDiagram A d) :
    (SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)) ⟶
      derivedInfinityCategory A :=
  (functorVertexEquiv _ _).symm
    ((strictComplexDiagramFamily A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))

/-- 同じ全図式評価の頂点を復元する。 -/
lemma strictDiagramEvaluatedDiagram_vertex (X : StrictComplexDiagram A d) :
    functorVertex (strictDiagramEvaluatedDiagram A d X) =
      (strictComplexDiagramFamily A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X) :=
  (functorVertexEquiv _ _).apply_symm_apply _

/-- 元の局所化評価と strict 評価を結ぶ、同じ全関手同型の成分。 -/
def strictDiagramEvaluatedEndpointIso (X : StrictComplexDiagram A d) :
    VertexIso
      ((strictDiagramDerivedEvaluation A d).app (Opposite.op ⦋0⦌)
        ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X)))
      (functorVertex (strictDiagramEvaluatedDiagram A d X)) :=
  (strictDiagramDerivedEvaluation_factor A d).app (ComposableArrows.mk₀ X) ≪≫
    eqToIso (congrArg HomotopyCategory.mk (strictDiagramEvaluatedDiagram_vertex A d X).symm)

/-- RR01：元の実 frame から元の coherent 図式の end 切断への実際の全単体的比較。
この宣言は比較射の同値性を主張しない。 -/
def strictDiagramFrameEndComparison (X Y : StrictComplexDiagram A d) :
    (SSet.uliftFunctor.{u + 1, u}).obj (strictDiagramFrameMapping A d X Y) ⟶
      simplicialSections (functorEndProjection
        (strictDiagramEvaluatedDiagram A d X) (strictDiagramEvaluatedDiagram A d Y)) :=
  (strictDiagramSourceFramePinchedEquivalence A d X Y).hom ≫
    pinchedHomMap (strictDiagramDerivedEvaluation A d)
      ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
      ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Y)) ≫
    (pinchedEndpointEquivalence (strictDiagramEvaluatedEndpointIso A d X)
      (strictDiagramEvaluatedEndpointIso A d Y)).hom ≫
    functorPinchedEndMap (strictDiagramEvaluatedDiagram A d X) (strictDiagramEvaluatedDiagram A d Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
