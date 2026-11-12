module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeLeftAttachmentFace
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRightAttachmentFace
public import
  SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEdgeFamilyRetractionProjection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyEndpointTransport

/-!
概要：元の根辺三角形・四面体の初期族を、実際の付加辺による枝終点の前置像へ結ぶ。
方針：同じ付加辺面の相対円柱を制限し、両端の厳密な式だけで表示変更する。
規約：底の元の円柱と全時刻の共通評価を保持。使われ方：共通 end の全経路の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCommonHomFamily hp p c hc dB dC y

section
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily hp p c hc dB dC y
local notation "hL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "K" => (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 2))) ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection t q
local notation "hK" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction_section_fixed q t y L hL
local notation "Φ" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition c hc f (i ≫ p) rfl dB y
local notation "IB" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y
local notation "J" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q _ t (stdSimplex.δ (0 : Fin 2))
  (SSet.Edge.δ_zero_yonedaEquiv_symm e) y L hL

/-- 元の左枝終点の前置像は、同じ付加辺面の終端を普遍相対切断で戻した初期族。 -/
lemma specifiedCoconeLeftAttachmentPrecomposition : IB ≫ Φ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
      (SSet.Edge.δ_one_yonedaEquiv_symm e) y K hK := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchCommonInitialFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition q e y := (Category.assoc _ _ _).symm
    _ = J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition q e y :=
      congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition q e y)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily_target hp p c hc dB dC y).symm
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition_family q e y L hL

/-- 元の左根辺初期族から枝終点の前置像へ、同じ底の円柱を保って結ぶ。 -/
def specifiedCoconeLeftAttachmentInitialHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y) (IB ≫ Φ) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily_source hp p c hc dB dC y)
    (specifiedCoconeLeftAttachmentPrecomposition hp p c hc dB dC y).symm

/-- 両端の表示変更後も、元の同じ付加辺面の比較円柱を保持する。 -/
lemma specifiedCoconeLeftAttachmentInitialHomotopy_raw :
    (specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 比較の全時刻で、元の同じ共通 Hom 族を厳密に評価する。 -/
lemma specifiedCoconeLeftAttachmentInitialHomotopy_evaluation :
    (specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst _ Δ[1] ≫ V := by
  rw [specifiedCoconeLeftAttachmentInitialHomotopy_raw, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction_evaluation]
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_evaluation q c t (stdSimplex.δ (1 : Fin 2))
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily_source,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily_evaluation] at hv
  exact congrArg (fst _ Δ[1] ≫ ·) hv.symm

/-- 底は、元の同じ付加辺面の底の切断比較を始点へ制限した円柱そのもの。 -/
lemma specifiedCoconeLeftAttachmentInitialHomotopy_projection :
    (specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase t q L y hL) (SSet.yonedaEquiv.symm c ≫ q)
        (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgeBase_source q e) rfl).h := by
  rw [specifiedCoconeLeftAttachmentInitialHomotopy_raw]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction_baseCylinder q c t
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
end

section
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily hp p c hc dB dC y
local notation "hL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "K" => (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 2))) ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection t q
local notation "hK" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction_section_fixed q t y L hL
local notation "Φ" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition c hc g (j ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC y
local notation "IB" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchInitialHomFamily hp p c hc dB dC y
local notation "J" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q _ t (stdSimplex.δ (0 : Fin 2))
  (SSet.Edge.δ_zero_yonedaEquiv_symm e) y L hL

/-- 元の右枝終点の前置像は、同じ付加辺面の終端を普遍相対切断で戻した初期族。 -/
lemma specifiedCoconeRightAttachmentPrecomposition : IB ≫ Φ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
      (SSet.Edge.δ_one_yonedaEquiv_symm e) y K hK := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchCommonInitialFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition q e y := (Category.assoc _ _ _).symm
    _ = J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition q e y :=
      congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition q e y)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily_target hp p c hc dB dC y).symm
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgePrecomposition_family q e y L hL

/-- 元の右根辺初期族から枝終点の前置像へ、同じ底の円柱を保って結ぶ。 -/
def specifiedCoconeRightAttachmentInitialHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y) (IB ≫ Φ) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily_source hp p c hc dB dC y)
    (specifiedCoconeRightAttachmentPrecomposition hp p c hc dB dC y).symm

/-- 両端の表示変更後も、元の同じ付加辺面の比較円柱を保持する。 -/
lemma specifiedCoconeRightAttachmentInitialHomotopy_raw :
    (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction q c t (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 比較の全時刻で、元の同じ共通 Hom 族を厳密に評価する。 -/
lemma specifiedCoconeRightAttachmentInitialHomotopy_evaluation :
    (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst _ Δ[1] ≫ V := by
  rw [specifiedCoconeRightAttachmentInitialHomotopy_raw, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction_evaluation]
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_evaluation q c t (stdSimplex.δ (1 : Fin 2))
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily_source,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily_evaluation] at hv
  exact congrArg (fst _ Δ[1] ≫ ·) hv.symm

/-- 底は、元の同じ付加辺面の底の切断比較を始点へ制限した円柱そのもの。 -/
lemma specifiedCoconeRightAttachmentInitialHomotopy_projection :
    (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase t q L y hL) (SSet.yonedaEquiv.symm c ≫ q)
        (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialTotalEdgeBase_source q e) rfl).h := by
  rw [specifiedCoconeRightAttachmentInitialHomotopy_raw]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction_baseCylinder q c t
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
