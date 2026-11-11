module

public import SerrePositivity.KST.LocalizingInvariants.CompositionTriangleRelativePrism
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：元の相対三角形 prism を、同じ二つの図式間のホモトピーとして表示する。
方針：合成対応の三角形射影で同じ辺を写し、元の二単体の関手頂点へ端点を揃える。
規約：ホモトピーの全射は元の prism そのもの。使われ方：curry と自然性による貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.TriangleVertex

variable {X : SSet.{u}} {x y z : X _⦋0⦌} (e : X.Edge x y) (f : X.Edge y z)
  (s : X _⦋2⦌) (h₂ : X.δ 2 s = e.edge) (h₀ : X.δ 0 s = f.edge)

lemma vertex_triangle :
    (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x f)).app
      (Opposite.op ⦋0⦌) (vertex e f s h₂ h₀) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm s) := by
  have he := congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceCurry_triangle x f _ (family s)
      ((face s e h₂).trans (constant_edge e).symm) (face s f h₀))
  have hc : curry (family s) =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm s)) : (Δ[0] : SSet.{u}) ⟶ _) := by
    apply uncurry_injective
    rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    rfl
  rw [SSet.yonedaEquiv_comp, hc] at he
  exact he

end TriangleVertex
namespace TriangleComparison

variable {X : SSet.{u}} [Quasicategory X] {x y z : X _⦋0⦌}
  (e : X.Edge x y) (f : X.Edge y z) (s t : X _⦋2⦌)
  (hs₂ : X.δ 2 s = e.edge) (hs₀ : X.δ 0 s = f.edge)
  (ht₂ : X.δ 2 t = e.edge) (ht₀ : X.δ 0 t = f.edge)

def diagramEdge : ((ihom (Δ[2] : SSet.{u})).obj X).Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm s)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm t)) :=
  ((comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.map
    (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x f))).ofEq
      (TriangleVertex.vertex_triangle e f s hs₂ hs₀)
      (TriangleVertex.vertex_triangle e f t ht₂ ht₀)

def homotopy : SSet.Homotopy (SSet.yonedaEquiv.symm s) (SSet.yonedaEquiv.symm t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (diagramEdge e f s t hs₂ hs₀ ht₂ ht₀).toTruncated

lemma homotopy_map : (homotopy e f s t hs₂ hs₀ ht₂ ht₀).h =
    prism e f s t hs₂ hs₀ ht₂ ht₀ := by
  change uncurry (SSet.yonedaEquiv.symm
    ((comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.map
      (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x f))).edge) = _
  let j : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x f ⟶ (ihom (Δ[2] : SSet.{u})).obj X :=
    pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x f)
  have he : SSet.yonedaEquiv.symm
      ((comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.map j).edge =
    SSet.yonedaEquiv.symm (comparison e f s t hs₂ hs₀ ht₂ ht₀).edge.edge ≫ j := by
    exact (SSet.yonedaEquiv_symm_comp _ _).symm
  exact (congrArg uncurry he).trans (uncurry_natural_left _ _)

end TriangleComparison
end SerrePositivity.KST.LocalizingInvariants
