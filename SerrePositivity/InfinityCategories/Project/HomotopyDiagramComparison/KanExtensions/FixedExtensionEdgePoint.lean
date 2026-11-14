module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionEdgeTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PrismTransportPointEvaluation

/-!
概要：固定延長の全辺 prism を、同じ実際の延長を表す一点で評価する。
方針：包含後の相対関手の族を元の図式へ戻し、全族の輸送同型の成分も制限する。
規約：元の図式と全族の同型の射を保持する。使われ方：左三角形の二成分の同定。
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
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv

/-- 延長を表す一点で制限した全辺 prism は、同じ元の図式の辺への制限そのもの。 -/
lemma fixedExtensionEdgePrism_point (W : K ⟶ E) (hW : W ≫ p = β) (hWi : i ≫ W = v) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism p β i v hv k)
      (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W, hW, hWi⟩)) =
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ k ≫ W := by
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W, hW, hWi⟩
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (SSet.yonedaEquiv.symm x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) =
        fst K (Δ[0] : SSet.{u}) ≫ W := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry]
    rw [SSet.yonedaEquiv_symm_zero, SSet.const_comp, SSet.const_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex W
  change (Δ[1] ◁ SSet.yonedaEquiv.symm x) ≫
    ((k ▷ S) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv)) = _
  rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, hx, ← Category.assoc, whiskerRight_fst,
    Category.assoc]

variable [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B _⦋0⦌} (e : B.Edge a b)
  (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)

/-- 同じ全辺輸送同型の成分を、同じ prism の一点制限を使う比較へ移す。 -/
abbrev fixedExtensionEdgeTransportComponent_hom_arrow (x : S _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportComponent_hom_arrow p e
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource p β i v hv k e hk)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i v hv k e hk) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism p β i v hv k)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_ι p β i v hv k e hk).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_ι p β i v hv k e hk).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism_projection p β i v hv k e hk) x

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
