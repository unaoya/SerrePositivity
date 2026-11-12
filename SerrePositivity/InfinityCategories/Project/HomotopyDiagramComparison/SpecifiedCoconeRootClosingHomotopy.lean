module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootCancellation

/-!
概要：元の左右の長辺を結ぶ底・始点固定円柱を保持し、その終点の類の相殺を回収する。
方針：同じ共通根辺の延長を結ぶ円柱を選び、同じ可縮な空間の辺へ戻す。
規約：終点はまだ全時刻固定とは主張しない。使われ方：終点固定の全 Hom 比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma comparison_endpoint_congr {X Y : SSet.{u}} (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X)
    (F : X ⟶ Y) {x x' y y' : X _⦋0⦌} (hx : x = x') (hy : y = y') :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x y) F).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x' y') F).hom := by
  subst x' y'
  rfl

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint hp p c hc dB dC
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
local notation "ε" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z))

/-- 閉じる円柱の元の左長辺も、同じ共通余錐を始点とする。 -/
lemma specifiedCoconeRootClosingLeft_initial : a ≫ W = v :=
  (Category.assoc _ _ _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial hp p c hc dB dC)

local notation "hW" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC
local notation "hV" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC
local notation "hWi" => specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "hVi" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC

/-- 元の左長辺から同じ指定修正後の右長辺へ向かう、底・始点固定の実際の円柱。 -/
def specifiedCoconeRootClosingHomotopy : SSet.Homotopy W V :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension q β a _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_leftAnodyne v hv
    W V hW hV hWi hVi).choose

/-- 同じ元の共通根辺の底を全時刻で固定する。 -/
lemma specifiedCoconeRootClosingHomotopy_projection :
    (specifiedCoconeRootClosingHomotopy hp p c hc dB dC).h ≫ q =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ β :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension q β a _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_leftAnodyne v hv
    W V hW hV hWi hVi).choose_spec.1

/-- 始点も同じ元の共通余錐のまま、全時刻で固定する。 -/
lemma specifiedCoconeRootClosingHomotopy_initial :
    (a ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRootClosingHomotopy hp p c hc dB dC).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ v :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension q β a _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_leftAnodyne v hv
    W V hW hV hWi hVi).choose_spec.2

/-- 同じ閉じる円柱を、共通根辺の延長空間の実際の辺として保持する。 -/
def specifiedCoconeRootClosingExtensionEdge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge q β a v hv hW hV hWi hVi
    (specifiedCoconeRootClosingHomotopy hp p c hc dB dC)
    (specifiedCoconeRootClosingHomotopy_projection hp p c hc dB dC)
    (specifiedCoconeRootClosingHomotopy_initial hp p c hc dB dC)

/-- 展開すると同じ実際の閉じる円柱を回収する。 -/
lemma specifiedCoconeRootClosingExtensionEdge_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm
      (specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q β a v hv) =
      (specifiedCoconeRootClosingHomotopy hp p c hc dB dC).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge_uncurry _ _ _ _ _ _ _ _ _ _ _ _

/-- 同じ実際の円柱の終点の辺の類も、四因子の相殺によって恒等射である。 -/
lemma specifiedCoconeRootClosingExtensionEdge_endpoint_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      ((specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC).map F).toTruncated) =
      Arrow.mk (𝟙 (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map L ε).hom).left) := by
  have hE := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleEdgeEvaluation_hom hS F
    (specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC)
  have hC := comparison_endpoint_congr hS F
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction_actual hp p c hc dB dC).symm
    (show _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCorrectedRootVertex hp p c hc dB dC = _ from rfl)
  exact (congrArg Arrow.mk hE).trans (hC.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingComparisonIso_endpoint_hom_arrow hp p c hc dB dC))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
