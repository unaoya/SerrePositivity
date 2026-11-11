module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeNativeBaseTerminal
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalCosliceFiber

/-!
概要：元の rooted 全族と native 普遍全族を、同じ全 Hom の終端係数を保って比較する。
方針：同じパラメータ・点図式の厳密な式から、最後の頂点制限の自明 Kan fiber で結ぶ。
規約：最後の頂点を全時刻固定し、付加辺の終端固定までは仮定しない。
使われ方：同じ全族間円柱の二面を用いた native 指定経路の照合。
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
local notation "Q" => Iso.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) d y)

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v ht y
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagramFamily hp p c hc dB dC y
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNativeFamily hp p c hc dB dC y

/-- 元の左 rooted 全族と native 普遍全族は、同じ全 Hom の終端上で結べる。 -/
lemma exists_specifiedCoconeLeftNativeUniversalComparison :
    ∃ H : SSet.Homotopy N U, H.h ≫ R = fst T Δ[1] ≫ Q := by
  have := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_of_rightAnodyne σ v _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleTerminalVertex_rightAnodyne
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) ht y
  have he : N ≫ R = U ≫ R :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagramFamily_terminal hp p c hc dB dC y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNativeFamily_terminal hp p c hc dB dC y).symm
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration R N U he
  refine ⟨H, ?_⟩
  exact hH.trans (congrArg (fst T Δ[1] ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNativeFamily_terminal hp p c hc dB dC y))

/-- 同じ左の実際の全族を、最後の頂点を全時刻固定する一つの円柱で結ぶ。 -/
def specifiedCoconeLeftNativeUniversalComparison : SSet.Homotopy N U :=
  (exists_specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y).choose

/-- 全族間の同じ比較円柱は、元の全 Hom の終端係数を全時刻固定する。 -/
lemma specifiedCoconeLeftNativeUniversalComparison_terminal :
    (specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y).h ≫ R = fst T Δ[1] ≫ Q :=
  (exists_specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y).choose_spec
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNative_tip hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v ht y
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagramFamily hp p c hc dB dC y
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNativeFamily hp p c hc dB dC y

/-- 元の右 rooted 全族と native 普遍全族は、同じ全 Hom の終端上で結べる。 -/
lemma exists_specifiedCoconeRightNativeUniversalComparison :
    ∃ H : SSet.Homotopy N U, H.h ≫ R = fst T Δ[1] ≫ Q := by
  have := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_of_rightAnodyne σ v
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronTerminalVertex_rightAnodyne
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) ht y
  have he : N ≫ R = U ≫ R :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagramFamily_terminal hp p c hc dB dC y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNativeFamily_terminal hp p c hc dB dC y).symm
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration R N U he
  refine ⟨H, ?_⟩
  exact hH.trans (congrArg (fst T Δ[1] ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNativeFamily_terminal hp p c hc dB dC y))

/-- 同じ右の実際の全族を、最後の頂点を全時刻固定する一つの円柱で結ぶ。 -/
def specifiedCoconeRightNativeUniversalComparison : SSet.Homotopy N U :=
  (exists_specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y).choose

/-- 全族間の同じ比較円柱は、元の全 Hom の終端係数を全時刻固定する。 -/
lemma specifiedCoconeRightNativeUniversalComparison_terminal :
    (specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y).h ≫ R = fst T Δ[1] ≫ Q :=
  (exists_specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y).choose_spec
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
