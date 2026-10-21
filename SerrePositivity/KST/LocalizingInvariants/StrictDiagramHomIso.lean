module

public import SerrePositivity.InfinityCategories.F2.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.F2.PrismHomotopy
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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [Quasicategory (SimplicialNerve C)] {F G : I ⥤ C} (η : F ⟶ G)
  (hη : ∀ i, IsInvertibleEdge (coherentNerveEdge (η.app i)))

def strictDiagramHomotopy := F2.prismHomotopy (F2.strictCoherentNatTransMap η)
  (F2.strictCoherentNatTransMap_zero _) (F2.strictCoherentNatTransMap_one _)

include hη in
lemma strictDiagramHomotopy_vertical
    (x : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (strictDiagramHomotopy η) x).toTruncated := by
  have he := F2.prismHomotopy_vertical (F2.strictCoherentNatTransMap η)
    (F2.strictCoherentNatTransMap_zero _) (F2.strictCoherentNatTransMap_one _) x
  exact (isInvertibleEdge_congr (e :=
    (simplicialHomotopyVertexEdge (strictDiagramHomotopy η) x).toTruncated)
    (f := edgeOfSimplex _) he).mpr
      (F2.strictCoherentNatTransMap_vertical_isInvertible η hη x)

def strictDiagramHomIso : FunctorIso (strictCoherentDiagram F) (strictCoherentDiagram G) :=
  functorIsoOfPointwiseInvertibleHomotopy (strictDiagramHomotopy η)
    (strictDiagramHomotopy_vertical η hη)

lemma strictDiagramHomIso_hom : (strictDiagramHomIso η hη).hom =
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (strictDiagramHomotopy η)) := rfl

end SerrePositivity.KST.LocalizingInvariants
