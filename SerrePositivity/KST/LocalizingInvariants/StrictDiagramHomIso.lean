module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PrismHomotopy
public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberRightShape

/-!
概要：成分が可逆な通常の自然変換の元の coherent prism の類を、実関手同型にする。
方針：全頂点での元の辺の可逆性を使い、同じホモトピーの辺の類で asIso を取る。
規約：既存の存在的同型へ置き換えない。使われ方：置換後の厳密 cospan 比較を逆にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [Quasicategory (SimplicialNerve C)] {F G : I ⥤ C} (η : F ⟶ G)
  (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app i)))

def strictDiagramHomotopy := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one _)

include hη in
lemma strictDiagramHomotopy_vertical
    (x : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (strictDiagramHomotopy η) x).toTruncated := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy_vertical (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one _) x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (strictDiagramHomotopy η) x).toTruncated)
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex _) he).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_vertical_isInvertible η hη x)

def strictDiagramHomIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (strictDiagramHomotopy η)
    (strictDiagramHomotopy_vertical η hη)

lemma strictDiagramHomIso_hom : (strictDiagramHomIso η hη).hom =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (strictDiagramHomotopy η)) := rfl

end SerrePositivity.KST.LocalizingInvariants
