module
public import SerrePositivity.KST.SConstruction.CoherentComparisonEdgeNaturality
public import SerrePositivity.KST.SConstruction.CoherentSimplexInsertionEdges

/-! # 標準合成面と元の恒等面の比較辺の定数性
概要：元の標準合成面・恒等面の比較辺は、同じ通常射の頂点の恒等辺になる。
方針：標準合成面の全 Path 作用の定数性と、退化の再添字自然性を使う。
規約：比較辺の全一単体を計算し、辺の成分だけの一致には置き換えない。
使われ方：元の比較四面体の二経路の定数因子を除き、指定 BF 比較辺を回収する。
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

/-- 最初の切断点が始点自身なら、元の Path 比較辺全体は恒等包含。 -/
lemma coherentEndpointPathLeftUnit_edge {J : Type u} [LinearOrder J] {a b : J} (hab : a ≤ b) :
    (nerve.edgeMk (coherentEndpointPathToComposite (show a ≤ a from le_rfl) hab)).edge =
      (nerve.edgeMk (𝟙 (coherentEndpointPath hab))).edge := by
  refine ComposableArrows.ext₁ rfl ?_ ?_
  · apply SimplicialThickening.Path.ext
    ext x
    change ((x = a ∨ x = a) ∨ (x = a ∨ x = b)) ↔ (x = a ∨ x = b)
    tauto
  · apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

/-- 始点での退化の全比較辺は、復号した同じ通常射の頂点の恒等辺。 -/
lemma coherentSimplexCompositionEdge_leftUnit
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
    (s : (SimplicialNerve C) _⦋n⦌) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (coherentSimplexCompositionEdge s i i j le_rfl hij).edge =
      (SSet.Edge.id (SimplicialCategory.homEquiv' _ _ (coherentSimplexArrow s i j hij))).edge := by
  exact (congrArg ((s.map (.mk (ULift.up i)) (.mk (ULift.up j))).app (Opposite.op ⦋1⦌))
    (coherentEndpointPathLeftUnit_edge
      (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij))).trans
        (coherentSimplexEndpointIdentity_edge s i j hij)

/-- 元の通常の標準合成面の全比較辺は、通常の合成射の同じ頂点の恒等辺。 -/
lemma coherentNerveCompStruct_comparison_edge_heq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (coherentSimplexCompositionEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex
      0 1 2 (by decide) (by decide)).edge
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge := by
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Z (f ≫ g)) 1)
    (SSet.Edge.id (SimplicialCategory.homEquiv' X Z (f ≫ g))).edge
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)

/-- 元の左恒等合成面の全比較辺も、元の同じ通常射の頂点の恒等辺。 -/
lemma coherentNerveIdComp_comparison_edge_heq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) :
    HEq (coherentSimplexCompositionEdge
      (SSet.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)).simplex
      0 1 2 (by decide) (by decide)).edge
      (SSet.Edge.id (SimplicialCategory.homEquiv' X Y f)).edge := by
  have hn := coherentSimplexCompositionEdge_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge
    (SimplexCategory.σ (0 : Fin 2)) 0 1 2 (by decide) (by decide)
  have hu := coherentSimplexCompositionEdge_leftUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge 0 1 (by decide)
  have hc := congrArg (fun k : X ⟶ Y =>
    (SSet.Edge.id (SimplicialCategory.homEquiv' X Y k)).edge) (coherentSimplexArrow_edge f)
  exact (heq_of_eq hn).trans ((heq_of_eq hu).trans (heq_of_eq hc))

end SerrePositivity.KST.SConstruction
