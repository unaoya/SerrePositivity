module
public import SerrePositivity.InfinityCategories.Core.RelativeInternalHomTrivialFibration

/-! # 可縮な実 Kan 標的に対する、指定部分族への制限の全境界持ち上げ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 可縮な標的では、任意の単射に沿う全関手族の制限は trivial Kan fibration。 -/
theorem contractibleTargetRestriction_trivialKanFibration {A B Z : SSet.{u}}
    (i : A ⟶ B) [Mono i] (hZ : IsContractibleKan Z) :
    TrivialKanFibration ((pre i).app Z) := by
  letI contractibleTargetToPoint : TrivialKanFibration (terminal.from Z) :=
    (isContractibleKan_iff_trivialKanFibration Z).mp hZ
  exact trivialKanFibration_pullbackObjObjπ i (terminal.from Z)
    (Functor.PullbackObjObj.ofIsTerminal internalHom i (terminal.from Z) terminalIsTerminal)

end SerrePositivity.KST.Fibration
