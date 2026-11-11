module
public import SerrePositivity.KST.Fibration.VerdierNullCompositeVertices
public import SerrePositivity.KST.Fibration.VerdierNullHomComparisonPrism

/-! # 元の比較円柱の合成頂点の実辺と、指定包含・商の零合成の全自然同値 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定二胞体の比較円柱を、同じ合成 path の頂点で評価した元の実辺。 -/
def verdierNullCompositeEdge (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    SSet.Edge (verdierNullCompositeVertex d j) (verdierNullCompositeVertex d k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierNullHomRelativeComparison d j k).edge)
      (ComposableArrows.mk₀ coherentTriangleFullPath)

/-- 元の合成頂点で評価した同じ実辺は、全 Kan Hom 内で可逆。 -/
theorem verdierNullCompositeEdge_isInvertible (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (verdierNullCompositeEdge d j k).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
    (verdierNullHomRelativeComparison d j k).edge
    (verdierNullHomRelativeComparison d j k).invertible _

/-- 元の Kan Hom の実可逆辺を、同じ実完全射間の全自然同値として回収する。 -/
def stableHomVertexEdgeFunctorIso {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    {v w : (A ⟶[SSet.{u}] B) _⦋0⦌} (e : SSet.Edge v w)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (stableHomExactMap v).hom (stableHomExactMap w).hom := by
  let q := stableHomAmbient A B
  let a := e.toTruncated.map ((truncation 2).map q)
  letI stableHomAmbientEdgeIso : IsIso (Truncated.HomotopyCategory.homMk a) := he.map q
  let E := asIso (Truncated.HomotopyCategory.homMk a)
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk (stableHomAmbient_vertex v))).symm ≪≫
    E ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk (stableHomAmbient_vertex w))

/-- 元の指定両端で、比較円柱の合成頂点の同じ実辺から得る全自然同値。 -/
def verdierNullCompositeOriginalIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierNullCompositeOriginalMap d j).hom
      (verdierNullCompositeOriginalMap d k).hom :=
  exactMapTransportFunctorIso (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)
    (stableHomVertexEdgeFunctorIso (verdierNullCompositeEdge d j k)
      (verdierNullCompositeEdge_isInvertible d j k))

/-- 指定した元の包含・商の零合成を、元の上側合成との全自然同値で回収する。 -/
def verdierNullCompositeIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.inclusion.hom ≫ d.projection.hom) (verdierNullCompositeOriginalMap d 0).hom := by
  have E := verdierNullCompositeOriginalIso d 1 0
  have he := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right => f.hom)
    (verdierNullCompositeOriginalMap_lower d)
  change (verdierNullCompositeOriginalMap d 1).hom = d.inclusion.hom ≫ d.projection.hom at he
  exact he ▸ E

/-- 比較円柱の合成 path 上の制限は、回収した同じ実合成辺の全時刻の評価である。 -/
theorem verdierNullHomComparisonPrism_composite (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (Δ[1] ◁ (SSet.const (ComposableArrows.mk₀ coherentTriangleFullPath) :
      (Δ[0] : SSet.{u}) ⟶ _)) ≫ verdierNullHomComparisonPrism d j k =
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (verdierNullCompositeEdge d j k).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_const
    (SSet.Edge.ofTruncated (verdierNullHomRelativeComparison d j k).edge)
    (A := (Δ[0] : SSet.{u})) (ComposableArrows.mk₀ coherentTriangleFullPath)
  exact h.trans (congrArg (fun t => fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
    SSet.yonedaEquiv.symm t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge (verdierNullHomRelativeComparison d j k).edge
        (ComposableArrows.mk₀ coherentTriangleFullPath)).symm)

end SerrePositivity.KST.Fibration
