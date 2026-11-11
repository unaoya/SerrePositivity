module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionEdgeTransport
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRightPrefixTriangleExtension
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismTransportIdentity

/-!
概要：右初面三角形の全持ち上げの終端辺から、終点評価と中間評価の輸送比較を構成する。
方針：同じ全族の辺 prism を使い、実際の右初面比較辺に対する自然性の正方形を得る。
規約：底の元の右初面脚と実際の比較辺を保持する。使われ方：付加辺・制限自然性の合成式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "σ" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "β" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σ)
local notation "i₀" => stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)

omit [Mono g] in
/-- 右初面三角形の終端辺の底は、元の native span の右初面脚そのもの。 -/
lemma specifiedCoconeRightPrefixTerminalEdge_base :
    stdSimplex.δ (0 : Fin 3) ≫ β = SSet.yonedaEquiv.symm (e).edge := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, (σ).d₀]

local notation "he" => specifiedCoconeRightPrefixTerminalEdge_base hp p c hc dB dC

/-- 同じ全持ち上げの終端辺を使う、元の右初面脚上の全族の prism。 -/
def specifiedCoconeRightPrefixTerminalPrism : (Δ[1] : SSet.{u + 1}) ⊗ S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (f ≫ (i ≫ p))
  :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism q β i₀ v hv (stdSimplex.δ (0 : Fin 3))

/-- 右初面三角形の中間頂点で評価した、共通余錐空間の同じ全族。 -/
def specifiedCoconeRightPrefixMiddleEvaluation : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p)) dC.vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he

/-- 右初面三角形の終点で評価した、同じ全族。 -/
def specifiedCoconeRightPrefixTerminalEvaluation : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p)) z :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he

/-- 全族の終点評価と中間評価の右初面脚による輸送を、同じ終端辺 prism で結ぶ同型。 -/
def specifiedCoconeRightPrefixTerminalTransportIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC)
      (specifiedCoconeRightPrefixMiddleEvaluation hp p c hc dB dC ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q e) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTransportIso q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he

local notation "x" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC
/-- 同じ延長空間の辺に沿う自然性。実際の右初面比較辺にもそのまま適用できる。 -/
abbrev specifiedCoconeRightPrefixTerminalTransport_square
    {ξ η : S _⦋0⦌} (s : (S).Edge ξ η) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTransportIso_naturality q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he s

/-- 実際の三角形の中間評価は、同じ三角形の中間頂点の値そのもの。 -/
lemma specifiedCoconeRightPrefixMiddleEvaluation_actual_val :
    ((specifiedCoconeRightPrefixMiddleEvaluation hp p c hc dB dC).app _ x).val =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC).app _ (stdSimplex.obj₀Equiv.symm
        1) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_vertex_val q β i₀ v hv
    (stdSimplex.δ (0 : Fin 3)) e he (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)
  exact h

/-- 終点評価も、同じ実際の右初面三角形の最後の頂点の値そのもの。 -/
lemma specifiedCoconeRightPrefixTerminalEvaluation_actual_val :
    ((specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC).app _ x).val =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC).app _ (stdSimplex.obj₀Equiv.symm
        2) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_vertex_val q β i₀ v hv
    (stdSimplex.δ (0 : Fin 3)) e he (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
