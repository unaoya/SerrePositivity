module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitSpanBoundaryFactors
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ContractibleFactorCancellation
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeStandardRootComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeCorrectionClass

/-!
概要：共通根辺の左右・中央・指定修正の四因子を、元の境界同型の定義で相殺する。
方針：各因子の既存の点評価を使い、可縮な始域での正準比較を分解する。
規約：終点の一致だけから恒等を推論しない。使われ方：全 Hom 族の評価固定比較の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
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
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint hp p c hc dB dC
local notation "uL" => NatTrans.app (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC) _
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC)
local notation "sL" => NatTrans.app (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC) _
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC)
local notation "uR" => NatTrans.app
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC) _
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC)
local notation "sR" => NatTrans.app
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC) _
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "M" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanMiddleBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanBoundaryIso c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "v₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl
local notation "eB" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
local notation "ε" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z))

/-- 左因子の終点は、同じ結合順序に揃えた境界・付加輸送の評価である。 -/
abbrev specifiedCoconeRootLeftFactor_hom_arrow :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootComparisonIso_boundary_hom_arrow hp p c hc dB dC).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexIso_map_hom_arrow ε
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftBoundaryFactor_hom_arrow c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)).symm

/-- 中央因子の終点は、元の native 比較の同じ一点制限の評価である。 -/
abbrev specifiedCoconeRootMiddleFactor_hom_arrow :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeStandardRootComparisonIso_endpoint_hom_arrow hp p c hc dB dC).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoComponent_point_hom_arrow
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportIso c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC q) v₀)

/-- 右因子の終点も、同じ結合順序に揃えた境界・付加輸送の評価である。 -/
abbrev specifiedCoconeRootRightFactor_hom_arrow :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootComparisonIso_boundary_hom_arrow hp p c hc dB dC).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexIso_map_hom_arrow ε
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightBoundaryFactor_hom_arrow c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)).symm

/-- 同じ指定四面体の修正後の長辺を、同じ共通根辺の空間の頂点として保持する。 -/
def specifiedCoconeCorrectedRootVertex : (S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q β a v hv
    ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC⟩

/-- 右の実際の長辺から同じ修正後長辺への比較は、元の指定境界同型を評価する。 -/
lemma specifiedCoconeRootCorrectionFactor_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ((hS).vertexIso uR
      (specifiedCoconeCorrectedRootVertex hp p c hc dB dC)) F).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map K ε).hom := by
  have h := comparison_endpoint_congr hS F
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction_actual hp p c hc dB dC)
    (show specifiedCoconeCorrectedRootVertex hp p c hc dB dC = _ from rfl)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCorrectionCanonical_boundary_hom_arrow hp p c hc dB dC)

/-- 元の左長辺から同じ指定修正後の右長辺への、共通根辺内の正準比較。 -/
def specifiedCoconeRootClosingComparisonIso :=
  (hS).vertexIso uL (specifiedCoconeCorrectedRootVertex hp p c hc dB dC)

/-- 元の指定境界同型が四因子を相殺するので、この比較の終点の類は恒等射である。 -/
lemma specifiedCoconeRootClosingComparisonIso_endpoint_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (specifiedCoconeRootClosingComparisonIso hp p c hc dB dC) F).hom =
      Arrow.mk (𝟙 (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map L ε).hom).left) := by
  have hK := congrArg (fun I ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I ε)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanBoundaryIso_factors c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
  have hInv := hK.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexIso_map_inverse_threeFactors L M R ε)
  have hCorrection := (specifiedCoconeRootCorrectionFactor_hom_arrow hp p c hc dB dC).trans
    (congrArg (fun I ↦ Arrow.mk I.hom) hInv)
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleVertexIso_endpoint_cancel hS F uL sL sR uR
    (specifiedCoconeCorrectedRootVertex hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map L ε) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map M ε) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map R ε)
    (specifiedCoconeRootLeftFactor_hom_arrow hp p c hc dB dC)
    (specifiedCoconeRootMiddleFactor_hom_arrow hp p c hc dB dC)
    (specifiedCoconeRootRightFactor_hom_arrow hp p c hc dB dC) hCorrection

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
