module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeUniversalNativeFamilies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeNativeBaseDiagrams
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootPrecomposition
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NormalizedCosliceRestrictionComposition

/-!
概要：元の rooted 全族の最後の頂点係数を、同じ指定余錐の全 Hom 表示へ厳密に回収する。
方針：同じ native 全族の根辺とその終端の二段制限を合成する。
規約：元の根辺全族を保持。使われ方：native 普遍全族との同じ終端上での比較。
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
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "root" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "rt" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "Q" => Iso.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) d y)

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagramFamily hp p c hc dB dC y
local notation "hr" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC

/-- 左の元の rooted 全族の終端係数は、native 普遍族と同じ元の全 Hom の係数である。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_terminal :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v ht y = Q := by
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_twoStep σ (stdSimplex.δ (1 : Fin 3)) root hr
    (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) rt v
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleTip_longEdge.symm ht y
  calc
    _ = N ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ (stdSimplex.δ (1 : Fin 3)) hr y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y) :=
      congrArg (N ≫ ·) hcomp.symm
    _ = (N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ (stdSimplex.δ (1 : Fin 3)) hr y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      (Category.assoc _ _ _).symm
    _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagramFamily_root hp p c hc dB dC y)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily_target hp p c hc dB dC y
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagramFamily hp p c hc dB dC y
local notation "hr" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNative_tip hp p c hc dB dC

/-- 右の元の rooted 全族の終端係数は、native 普遍族と同じ元の全 Hom の係数である。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_terminal :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v ht y = Q := by
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_twoStep σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge) root hr
    (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) rt v
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge_target_terminalFace ht y
  calc
    _ = N ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge) hr y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y) :=
      congrArg (N ≫ ·) hcomp.symm
    _ = (N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge) hr y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      (Category.assoc _ _ _).symm
    _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagramFamily_root hp p c hc dB dC y)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily_target hp p c hc dB dC y
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
