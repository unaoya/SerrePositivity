module
public import SerrePositivity.KST.NonConnective.DGSuspensionEdgeIsoTransport
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：指定された可逆二胞体を通して、同じ元の辺の可逆性を輸送する。
方針：元の h への自然同型を指定辺へ評価し、区間模型の包含へ特殊化する。
規約：辺比較を厳密等号へ強めない。
使われ方：K-7 e の B1 全反復作用の Morita 辺の可逆性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective

/-- 可逆な関手比較の両像は同じ指定辺に対し同値性を同時に持つ。 -/
theorem suspensionFunctorIso_isInvertible_iff {X Y : SSet.{u}}
    [Quasicategory Y] {f g : X ⟶ Y} (i : FunctorIso f g)
    {x y : X _⦋0⦌} (e : X.Edge x y) :
    IsInvertibleEdge (e.map f) ↔ IsInvertibleEdge (e.map g) := by
  exact NatIso.isIso_map_iff i.toNatIso (Truncated.HomotopyCategory.homMk e.toTruncated)

/-- 同じ区間写像空間内の指定可逆比較は、元の辺の可逆性を保つ。 -/
theorem suspensionEdgeIso_isInvertible_iff {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {e f : X.Edge x y}
    (i : VertexIso (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f)) :
    IsInvertibleEdge e ↔ IsInvertibleEdge f := by
  have j : FunctorIso (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm f.edge) :=
    VertexIso.map i (vertexFiberι _ _)
  have h := suspensionFunctorIso_isInvertible_iff j (SSet.Edge.ofTruncated homotopyIntervalEdge)
  have hr (k : X.Edge x y) : ((SSet.Edge.ofTruncated homotopyIntervalEdge).map
      (SSet.yonedaEquiv.symm k.edge)).edge = k.edge := by
    have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
      apply stdSimplex.objEquiv.injective
      ext a
      fin_cases a <;> rfl
    change (SSet.yonedaEquiv.symm k.edge).app (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge = _
    rw [← hi, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  exact (isInvertibleEdge_congr (e := (SSet.Edge.ofTruncated homotopyIntervalEdge).map
    (SSet.yonedaEquiv.symm e.edge)) (f := e) (hr e)).symm.trans
      (h.trans (isInvertibleEdge_congr (e := (SSet.Edge.ofTruncated homotopyIntervalEdge).map
        (SSet.yonedaEquiv.symm f.edge)) (f := f) (hr f)))

end SerrePositivity.KST.NonConnective
