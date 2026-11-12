module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeNativeUniversalComparisons

/-!
概要：元の rooted 全族と native 普遍全族の同じ比較円柱を、付加辺面と根辺へ制限する。
方針：同じ正規化制限へ後合成し、二段制限の式で終端係数を回収する。
規約：根辺の終端固定と付加辺の動く終端を区別する。使われ方：同じ二面の自然性正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y
local notation "root" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "rt" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "Q" => Iso.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) d y)

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNativeFamily hp p c hc dB dC y
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "face" => stdSimplex.δ (2 : Fin 3)
local notation "af" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC
local notation "rf" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily hp p c hc dB dC y
local notation "hF" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "Ra" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ face af y
local notation "Rr" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ (stdSimplex.δ (1 : Fin 3)) rf y

/-- 左の同じ全族間円柱を、元の付加辺面の底から native 普遍族の同じ面へ制限する。 -/
def specifiedCoconeLeftNativeUniversalAttachmentFace : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase t q F y hF) (U ≫ Ra) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H Ra)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagramFamily_attachment hp p c hc dB dC y) rfl

/-- 付加辺面の raw な円柱は、元の同じ全族間円柱の制限そのものである。 -/
lemma specifiedCoconeLeftNativeUniversalAttachmentFace_raw :
    (specifiedCoconeLeftNativeUniversalAttachmentFace hp p c hc dB dC y).h = (H).h ≫ Ra :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 左の同じ全族間円柱を、元の根辺全族から native 普遍族の同じ根辺へ制限する。 -/
def specifiedCoconeLeftNativeUniversalRootFace : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y) (U ≫ Rr) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H Rr)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagramFamily_root hp p c hc dB dC y) rfl

/-- 根辺の raw な円柱も、元の同じ全族間円柱の制限そのものである。 -/
lemma specifiedCoconeLeftNativeUniversalRootFace_raw :
    (specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y).h = (H).h ≫ Rr :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 根辺面では、元の同じ全 Hom の終端係数を全時刻固定する。 -/
lemma specifiedCoconeLeftNativeUniversalRootFace_terminal :
    (specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y =
      fst T Δ[1] ≫ Q := by
  rw [specifiedCoconeLeftNativeUniversalRootFace_raw]
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_twoStep σ (stdSimplex.δ (1 : Fin 3)) root rf
    (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) rt v _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleTip_longEdge.symm ht y
  exact (Category.assoc (H).h Rr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y)).trans
      ((congrArg ((H).h ≫ ·) hcomp).trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalComparison_terminal hp p c hc dB dC y))

/-- 付加辺面の動く終端も、同じ全族間円柱の中頂点の制限として厳密に保持する。 -/
lemma specifiedCoconeLeftNativeUniversalAttachmentFace_terminal :
    (specifiedCoconeLeftNativeUniversalAttachmentFace hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (t ≫ q) (stdSimplex.δ (0 : Fin 2)) rfl y =
      (H).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ ((stdSimplex.δ (0 : Fin 2)) ≫ face)
        ((Category.assoc _ _ _).trans (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y := by
  rw [specifiedCoconeLeftNativeUniversalAttachmentFace_raw]
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_twoStep σ face (t ≫ q) af
    (stdSimplex.δ (0 : Fin 2)) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q)) rfl
    ((stdSimplex.δ (0 : Fin 2)) ≫ face) rfl
    ((Category.assoc _ _ _).trans (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y
  exact (Category.assoc (H).h Ra
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (t ≫ q) (stdSimplex.δ (0 : Fin 2)) rfl y)).trans
      (congrArg ((H).h ≫ ·) hcomp)
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNativeFamily hp p c hc dB dC y
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "face" => stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)
local notation "af" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC
local notation "rf" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNative_tip hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily hp p c hc dB dC y
local notation "hF" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "Ra" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ face af y
local notation "Rr" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge) rf y

/-- 右の同じ全族間円柱を、元の付加辺面の底から native 普遍族の同じ面へ制限する。 -/
def specifiedCoconeRightNativeUniversalAttachmentFace : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase t q F y hF) (U ≫ Ra) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H Ra)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagramFamily_attachment hp p c hc dB dC y) rfl

/-- 付加辺面の raw な円柱は、元の同じ全族間円柱の制限そのものである。 -/
lemma specifiedCoconeRightNativeUniversalAttachmentFace_raw :
    (specifiedCoconeRightNativeUniversalAttachmentFace hp p c hc dB dC y).h = (H).h ≫ Ra :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 右の同じ全族間円柱を、元の根辺全族から native 普遍族の同じ根辺へ制限する。 -/
def specifiedCoconeRightNativeUniversalRootFace : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y) (U ≫ Rr) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H Rr)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagramFamily_root hp p c hc dB dC y) rfl

/-- 根辺の raw な円柱も、元の同じ全族間円柱の制限そのものである。 -/
lemma specifiedCoconeRightNativeUniversalRootFace_raw :
    (specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y).h = (H).h ≫ Rr :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 根辺面では、元の同じ全 Hom の終端係数を全時刻固定する。 -/
lemma specifiedCoconeRightNativeUniversalRootFace_terminal :
    (specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y =
      fst T Δ[1] ≫ Q := by
  rw [specifiedCoconeRightNativeUniversalRootFace_raw]
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_twoStep σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge) root rf
    (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) rt v
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge_target_terminalFace ht y
  exact (Category.assoc (H).h Rr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y)).trans
      ((congrArg ((H).h ≫ ·) hcomp).trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalComparison_terminal hp p c hc dB dC y))

/-- 付加辺面の動く終端も、同じ全族間円柱の中頂点の制限として厳密に保持する。 -/
lemma specifiedCoconeRightNativeUniversalAttachmentFace_terminal :
    (specifiedCoconeRightNativeUniversalAttachmentFace hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (t ≫ q) (stdSimplex.δ (0 : Fin 2)) rfl y =
      (H).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ ((stdSimplex.δ (0 : Fin 2)) ≫ face)
        ((Category.assoc _ _ _).trans (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y := by
  rw [specifiedCoconeRightNativeUniversalAttachmentFace_raw]
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_twoStep σ face (t ≫ q) af
    (stdSimplex.δ (0 : Fin 2)) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q)) rfl
    ((stdSimplex.δ (0 : Fin 2)) ≫ face) rfl
    ((Category.assoc _ _ _).trans (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y
  exact (Category.assoc (H).h Ra
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (t ≫ q) (stdSimplex.δ (0 : Fin 2)) rfl y)).trans
      (congrArg ((H).h ≫ ·) hcomp)
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
