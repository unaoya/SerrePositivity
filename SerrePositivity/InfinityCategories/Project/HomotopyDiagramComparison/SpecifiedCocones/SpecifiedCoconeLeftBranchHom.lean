module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeLeftHomTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.PointRestrictionFullHomCylinder

/-!
概要：元の左枝の全辺族から、同じ実際の左脚への評価固定 Hom 比較を構成する。
方針：枝の初期制限を評価固定で始対象の切断へ結び、底の同じ前合成へ射影する。
規約：標準 prism 自身の左辺と全 Hom の族を保持。使われ方：共通根辺との比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
  (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p)
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTransportEdge hp p c hc dB dC
local notation "U" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRestrictionEdgeApex i dB d k
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q dB y ≫
  Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q dB y)

/-- 元の左脚の前合成は、同じ枝の初期 Hom の底の前合成そのもの。 -/
lemma specifiedCoconeLeftBranchPrecomposition_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeApexHomPrecomposition dB d e y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBranchHomPrecomposition_eq dB d e y i rfl k rfl

/-- 元の左全辺族を、枝の始対象 dB の初期 Hom 空間へ移す。 -/
def specifiedCoconeLeftBranchInitialHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q dB y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionInitialHomFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y
local notation "I" => specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y

/-- 初期 Hom の包含後は、元の左全辺族の同じ初期頂点制限である。 -/
lemma specifiedCoconeLeftBranchInitialHomFamily_ι :
    I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm dB) ≫ q) y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftFullHomFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction
        (SSet.yonedaEquiv.symm (k).edge) (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm k) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionInitialHomFamily_ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y

/-- 中間族の評価は、元の全 Hom 族の左枝への制限そのもの。 -/
lemma specifiedCoconeLeftBranchInitialHomFamily_evaluation :
    I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q dB y = U :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionInitialHomFamily_evaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y

/-- 底へ射影すると、同じ元の左脚の実際の前合成を厳密に回収する。 -/
lemma specifiedCoconeLeftBranchInitialHomFamily_projection :
    I ≫ P = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeApexHomPrecomposition dB d e y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionInitialHomFamily_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y).trans
      (specifiedCoconeLeftBranchPrecomposition_eq hp p c hc dB dC y)

/-- 元の左全辺族の初期制限へ至る、評価上で全時刻定値な比較データ。 -/
def specifiedCoconeLeftBranchHomCylinderData : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationCylinder q dB y U hB I :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullHomCylinderData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y hB
local notation "H" => specifiedCoconeLeftBranchHomCylinderData hp p c hc dB hB dC y

/-- 元の左枝の Hom 比較を、同じ実際の左脚の前合成へ結ぶ円柱。 -/
def specifiedCoconeLeftBranchHomotopy : SSet.Homotopy
    (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison dB hB y) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeApexHomPrecomposition dB d e y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullHomCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y hB) rfl
    (specifiedCoconeLeftBranchPrecomposition_eq hp p c hc dB dC y)

/-- 左枝の比較は、保持した同じ評価固定中間円柱の raw な射影である。 -/
lemma specifiedCoconeLeftBranchHomotopy_projection :
    (specifiedCoconeLeftBranchHomotopy hp p c hc dB hB dC y).h = (H).homotopy.h ≫ P := by
  rw [specifiedCoconeLeftBranchHomotopy, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullHomCylinder_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) q r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) d k y hB

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
