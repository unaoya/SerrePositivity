module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionEdgeTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionHomotopyEdge

/-!
概要：固定延長の辺の両端評価を、相対関手の同じ頂点評価として計算する。
方針：全族の prism の端点を展開し、元の円柱の指定頂点の制限を回収する。
規約：元の円柱と辺の代表を変えない。使われ方：左三角形の中間評価の類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {K D E B : SSet.{u}} (p : E ⟶ B) (β : K ⟶ B)
  (i : D ⟶ K) (v : D ⟶ E) (hv : v ≫ p = i ≫ β) (k : (Δ[1] : SSet.{u}) ⟶ K)
  {a b : B _⦋0⦌} (e : B.Edge a b) (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv

/-- 全辺の始点評価は、同じ相対関手の始点頂点での評価である。 -/
lemma fixedExtensionEdgeSource_evaluate :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource p β i v hv k e hk ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (k.app _ (stdSimplex.obj₀Equiv.symm 0)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_ι, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism, ← Category.assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_whiskerRight, SSet.const_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_at_vertex p β (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) _).symm

/-- 全辺の終点評価も、同じ相対関手の終点頂点での評価である。 -/
lemma fixedExtensionEdgeTarget_evaluate :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (k.app _ (stdSimplex.obj₀Equiv.symm 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_ι, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism, ← Category.assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_whiskerRight, SSet.const_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_at_vertex p β (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) _).symm

variable {W W' : K ⟶ E} (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
  (H : SSet.Homotopy W W') (hH : H.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫ β)
  (hI : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst D (Δ[1] : SSet.{u}) ≫ v)
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge p β i v hv hW hW' hWi hWi' H hH hI

/-- 元の円柱を表す辺の始点評価は、同じ頂点で円柱を制限した raw な辺を保持する。 -/
lemma fixedExtensionEdgeSource_map_homotopy_raw :
    SSet.yonedaEquiv.symm ((s).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource p β i v hv k e hk)).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a =
      lift (SSet.const (k.app _ (stdSimplex.obj₀Equiv.symm 0))) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h := by
  change SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource p β i v hv k e hk).app _ (s).edge) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, fixedExtensionEdgeSource_evaluate]
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_at_vertex p β
    (SSet.yonedaEquiv.symm (s).edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv)
    (k.app _ (stdSimplex.obj₀Equiv.symm 0))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge_uncurry] at he
  simpa only [Category.assoc] using he

/-- 終点評価も、同じ元の円柱を指定終点で制限した raw な辺そのもの。 -/
lemma fixedExtensionEdgeTarget_map_homotopy_raw :
    SSet.yonedaEquiv.symm ((s).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk)).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      lift (SSet.const (k.app _ (stdSimplex.obj₀Equiv.symm 1))) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h := by
  change SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk).app _ (s).edge) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, fixedExtensionEdgeTarget_evaluate]
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_at_vertex p β
    (SSet.yonedaEquiv.symm (s).edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv)
    (k.app _ (stdSimplex.obj₀Equiv.symm 1))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge_uncurry] at he
  simpa only [Category.assoc] using he

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
