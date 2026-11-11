module
public import SerrePositivity.KST.SConstruction.PinchedComparisonCoordinate
public import SerrePositivity.KST.SConstruction.CoherentComparisonFaceEdges

/-! # 保存した pinched 比較面から元の豊穣辺全体を復号
概要：元の豊穣辺を写した指定比較面を復号すると、同じ元の全一単体を回収する。
方針：元の比較単体の豊穣作用と恒等区間の座標計算を使う。
規約：辺の類や成分ではなく全一単体を依存等号で回収する。局所 Kan 性は不要。
使われ方：合成面の復号辺と元の BF 比較辺を同じ比較四面体内で接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の Hom の一単体が作る比較面の一般復号辺は、元の全一単体そのもの。 -/
lemma coherentHomComparisonSimplex_edge_heq {X Y : C}
    (e : (SimplicialCategory.sHom X Y) _⦋1⦌) :
    HEq (coherentSimplexCompositionEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex e)
      0 1 2 (by decide) (by decide)).edge e := by
  change HEq ((SSet.yonedaEquiv.symm e).app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap.{u} (0 : Fin 2)).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (coherentEndpointPathToComposite (J := ULift.{u} (Fin 3))
        (show (ULift.up (0 : Fin 3) : ULift.{u} _) ≤ ULift.up 1 from by decide)
        (show (ULift.up (1 : Fin 3) : ULift.{u} _) ≤ ULift.up 2 from by decide))).edge)) e
  rw [pinchedComparisonCoordinate_edge]
  exact heq_of_eq (Equiv.apply_symm_apply SSet.yonedaEquiv e)

/-- 元の辺を写した指定比較面の全二単体は、同じ元の比較単体そのもの。 -/
lemma enrichedComparisonPinchedTriangle_original {X Y : C} {f g : X ⟶ Y}
    (e : (SimplicialCategory.sHom X Y).Edge
      (SimplicialCategory.homEquiv' _ _ f) (SimplicialCategory.homEquiv' _ _ g)) :
    (enrichedComparisonPinchedTriangle e).simplex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex e.edge := rfl

/-- 保存した指定比較面の復号辺全体は、元の同じ豊穣辺の全一単体を回収する。 -/
lemma enrichedComparisonPinchedTriangle_decoded_heq {X Y : C} {f g : X ⟶ Y}
    (e : (SimplicialCategory.sHom X Y).Edge
      (SimplicialCategory.homEquiv' _ _ f) (SimplicialCategory.homEquiv' _ _ g)) :
    HEq (coherentSimplexCompositionEdge (enrichedComparisonPinchedTriangle e).simplex
      0 1 2 (by decide) (by decide)).edge e.edge :=
  (coherentSimplexCompositionEdge_heq (enrichedComparisonPinchedTriangle_original e)
    0 1 2 (by decide) (by decide)).trans (coherentHomComparisonSimplex_edge_heq e.edge)

end SerrePositivity.KST.SConstruction
