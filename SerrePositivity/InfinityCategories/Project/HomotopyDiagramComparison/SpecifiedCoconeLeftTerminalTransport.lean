module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionEdgeTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeLeftTriangleExtension
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismTransportIdentity

/-!
概要：左三角形の全持ち上げの終端辺から、終点評価と中間評価の輸送比較を構成する。
方針：同じ全族の辺 prism を使い、実際の左比較辺に対する自然性の正方形を得る。
規約：底の元の左脚と実際の比較辺を保持する。使われ方：付加辺・制限自然性の合成式。
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
local notation "σ" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "β" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σ)
local notation "i₀" => stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial_base hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtensionSpace hp p c hc dB dC
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)

omit [Mono g] in
/-- 左三角形の終端辺の底は、元の native span の左脚そのもの。 -/
lemma specifiedCoconeLeftTerminalEdge_base :
    stdSimplex.δ (0 : Fin 3) ≫ β = SSet.yonedaEquiv.symm (e).edge := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, (σ).d₀]

local notation "he" => specifiedCoconeLeftTerminalEdge_base hp p c hc dB dC

/-- 同じ全持ち上げの終端辺を使う、元の左脚上の全族の prism。 -/
def specifiedCoconeLeftTerminalPrism : (Δ[1] : SSet.{u + 1}) ⊗ S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (f ≫ (i ≫ p)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism q β i₀ v hv (stdSimplex.δ (0 : Fin 3))

/-- 左三角形の中間頂点で評価した、共通余錐空間の同じ全族。 -/
def specifiedCoconeLeftMiddleEvaluation : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p)) dB.vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he

/-- 左三角形の終点で評価した、同じ全族。 -/
def specifiedCoconeLeftTerminalEvaluation : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p)) z :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he

/-- 全族の終点評価と中間評価の左脚による輸送を、同じ終端辺 prism で結ぶ同型。 -/
def specifiedCoconeLeftTerminalTransportIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC)
      (specifiedCoconeLeftMiddleEvaluation hp p c hc dB dC ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q e) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTransportIso q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he

local notation "x" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC
/-- 同じ延長空間の辺に沿う自然性。実際の左比較辺にもそのまま適用できる。 -/
abbrev specifiedCoconeLeftTerminalTransport_square
    {ξ η : S _⦋0⦌} (s : (S).Edge ξ η) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTransportIso_naturality q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) e he s

/-- 実際の三角形の中間評価は、同じ三角形の中間頂点の値そのもの。 -/
lemma specifiedCoconeLeftMiddleEvaluation_actual_val :
    ((specifiedCoconeLeftMiddleEvaluation hp p c hc dB dC).app _ x).val =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC).app _ (stdSimplex.obj₀Equiv.symm 1) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_vertex_val q β i₀ v hv
    (stdSimplex.δ (0 : Fin 3)) e he (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_projection hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial hp p c hc dB dC)
  exact h

/-- 終点評価も、同じ実際の左三角形の最後の頂点の値そのもの。 -/
lemma specifiedCoconeLeftTerminalEvaluation_actual_val :
    ((specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC).app _ x).val =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC).app _ (stdSimplex.obj₀Equiv.symm 2) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_vertex_val q β i₀ v hv
    (stdSimplex.δ (0 : Fin 3)) e he (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_projection hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
