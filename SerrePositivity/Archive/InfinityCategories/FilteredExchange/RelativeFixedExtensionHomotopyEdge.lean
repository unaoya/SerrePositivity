module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFixedExtensionCurry
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftEndpoint

/-!
概要：底と部分族を固定する元の実ホモトピーを同じ相対延長空間の実辺にする。
方針：同じ curry の一単体を使い、両端を元の延長頂点へ厳密に戻す。
規約：代表を選び直さない。
使われ方：元の全係数円柱と既存の指定比較の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ図式・部分族固定の実円柱は元の二延長頂点の間の実辺。 -/
def relativeFixedExtensionHomotopyEdge {D A E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) {f g : A ⟶ E} (H : SSet.Homotopy f g)
    (hf : f ≫ p = b) (hg : g ≫ p = b) (hif : i ≫ f = v) (hig : i ≫ g = v)
    (hB : H.h ≫ p = CartesianMonoidalCategory.fst A Δ[1] ≫ b)
    (hV : (i ▷ Δ[1]) ≫ H.h = CartesianMonoidalCategory.fst D Δ[1] ≫ v) :
    (relativeFunctorExtensionSpace p b i v hv).Edge
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨f, hf, hif⟩)
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨g, hg, hig⟩) := by
  refine SSet.Edge.mk (SSet.yonedaEquiv
    (relativeFixedExtensionCurry p b i v hv H.h hB hV)) ?_ ?_
  · apply Subtype.ext
    apply Subtype.ext
    exact (functorEdgeOfSimplicialHomotopy H).src_eq
  · apply Subtype.ext
    apply Subtype.ext
    exact (functorEdgeOfSimplicialHomotopy H).tgt_eq

/-- 可縮な Kan 延長空間では同じ二頂点間の指定同型は一意。 -/
lemma vertexIso_eq_of_contractible {K : SSet.{u}} (hK : IsContractibleKan K)
    {x y : K _⦋0⦌} (e e' : VertexIso x y) : e = e' := by
  have : KanComplex K := hK.kanComplex
  apply Iso.ext
  exact (hK.isTerminalVertex y).isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.F2
