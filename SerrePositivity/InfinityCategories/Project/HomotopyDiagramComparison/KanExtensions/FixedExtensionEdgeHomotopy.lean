module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionVertexEvaluation

/-!
概要：固定延長空間の任意の実際の辺を、同じ底・初期値を保つ円柱へ展開する。
方針：関手辺を uncurry し、fiber の包含後の全パラメータの等式を使う。
規約：同じ一単体を使う。使われ方：終点を厳密に固定する根辺比較円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma identityEdge_diagram {X : SSet.{u}} (z : X _⦋0⦌) :
    SSet.yonedaEquiv.symm (SSet.Edge.id (X := X) z).edge = (SSet.const z : Δ[1] ⟶ X) := by
  change SSet.yonedaEquiv.symm (X.σ 0 z) = _
  rw [← stdSimplex.σ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

variable {A D E B : SSet.{u}} (p : E ⟶ B) (β : A ⟶ B)
  (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
  {W W' : A ⟶ E} (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv).Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W, hW, hWi⟩)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W', hW', hWi'⟩))

/-- 同じ延長空間の実際の辺を、元の二つの図式の円柱にする。 -/
def fixedExtensionEdgeHomotopy : SSet.Homotopy W W' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge
    ((s.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β))).toTruncated)

/-- 円柱は同じ一単体の全族としての展開そのもの。 -/
lemma fixedExtensionEdgeHomotopy_raw :
    (fixedExtensionEdgeHomotopy p β i v hv hW hW' hWi hWi' s).h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        (SSet.yonedaEquiv.symm s.edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) := by
  change uncurry (SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β)).app _ s.edge)) = _
  rw [← SSet.yonedaEquiv_symm_comp]
  rfl

/-- 元の底の図式を全時刻で固定する。 -/
lemma fixedExtensionEdgeHomotopy_projection :
    (fixedExtensionEdgeHomotopy p β i v hv hW hW' hWi hWi' s).h ≫ p =
      fst A (Δ[1] : SSet.{u}) ≫ β := by
  rw [fixedExtensionEdgeHomotopy_raw]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection _

/-- 元の初期図式も全時刻で固定する。 -/
lemma fixedExtensionEdgeHomotopy_initial :
    (i ▷ (Δ[1] : SSet.{u})) ≫
        (fixedExtensionEdgeHomotopy p β i v hv hW hW' hWi hWi' s).h =
      fst D (Δ[1] : SSet.{u}) ≫ v := by
  rw [fixedExtensionEdgeHomotopy_raw, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι_pre, SSet.comp_const]
  change uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ β) v hv) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ β))) = _
  rw [SSet.const_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex v

variable (k : (Δ[1] : SSet.{u}) ⟶ A) {a b : B _⦋0⦌} (e : B.Edge a b)
  (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)

/-- 終点での辺は、同じ円柱の同じ頂点制限そのもの。 -/
lemma fixedExtensionEdgeHomotopy_endpoint_raw :
    SSet.yonedaEquiv.symm ((s.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk)).edge) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      lift (SSet.const (k.app _ (stdSimplex.obj₀Equiv.symm 1))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (fixedExtensionEdgeHomotopy p β i v hv hW hW' hWi hWi' s).h := by
  change SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk).app _ s.edge) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_evaluate]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_at_vertex p β
    (SSet.yonedaEquiv.symm s.edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv)
    (k.app _ (stdSimplex.obj₀Equiv.symm 1))
  rw [← fixedExtensionEdgeHomotopy_raw p β i v hv hW hW' hWi hWi' s] at h
  simpa only [Category.assoc] using h

/-- 終点の辺が厳密に恒等なら、同じ円柱の終点を全時刻で固定する。 -/
lemma fixedExtensionEdgeHomotopy_endpoint_constant (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (hs : (s.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk)).edge =
      (SSet.Edge.id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) z).edge) :
    lift (SSet.const (k.app _ (stdSimplex.obj₀Equiv.symm 1))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (fixedExtensionEdgeHomotopy p β i v hv hW hW' hWi hWi' s).h = SSet.const z.val := by
  rw [← fixedExtensionEdgeHomotopy_endpoint_raw p β i v hv hW hW' hWi hWi' s k e hk,
    hs, identityEdge_diagram, SSet.const_comp]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
