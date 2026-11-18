module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableFiniteLimitsColimits

/-!
概要：既存の点ごとの loop の全族を使い、安定係数の全関手圏の安定性を回収する。
方針：有限極限・零対象・指定 loop 同値を関手圏へ運び、既存の loop 判定へ入れる。
使われ方：HA Proposition 1.1.3.1、層の安定性を示す際の周囲の前層圏。
規約：始域は任意の単体集合。点ごとの任意選択を自然な図式と見なさない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 安定係数の全関手圏は、元の loop の全族によって安定である。 -/
theorem isStable_functorCategory (K X : SSet.{u}) [Quasicategory X] [IsStable X] :
    IsStable ((ihom K).obj X) := by
  letI : HasFiniteLimits X := hasFiniteLimits_of_isStable X
  letI : ZeroObjects.HasZeroVertex ((ihom K).obj X) := hasZeroVertex_functorCategory K X
  letI : HasFiniteLimits ((ihom K).obj X) := hasFiniteLimits_functorCategory K X
  let s := Classical.choose (trivialKanFibration_exists_section
    (loopDiagramEvaluation X 1 1))
  have hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X :=
    Classical.choose_spec (trivialKanFibration_exists_section (loopDiagramEvaluation X 1 1))
  let e := (suspensionLoopDiagramEquivalence X).symm.trans
    (suspensionDiagramSourceEquivalence X)
  have he : IsQCatEquivalence (loopDiagramEvaluation X 0 0) := by
    exact e.isQCatEquivalence
  have hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0) :=
    (loopDiagramSection_isQCatEquivalence s hs).comp he
  exact isStable_of_loopEquivalence (functorLoopSection K s)
    (functorLoopSection_target s hs) (functorLoopSection_loop_isQCatEquivalence s hΩ)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
