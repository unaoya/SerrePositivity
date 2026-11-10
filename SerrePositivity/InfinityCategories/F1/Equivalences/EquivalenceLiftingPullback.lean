module

public import SerrePositivity.InfinityCategories.Core.EquivalencePullbackPathLifting
public import SerrePositivity.InfinityCategories.F1B.Fibrations.EquivalenceLiftingInvertible
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativePathBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：同値を右に持ち上げる射に沿って、同じ同値写像を厳密に引き戻す。
方針：可逆辺の終点指定の持ち上げから相対 path の全境界持ち上げを得る。
規約：モデル構造の instance を仮定しない。
使われ方：実際の分類先の Hom の成分比較を同じ底へ引き戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 同値を右に持ち上げる射に沿う、元の同値の厳密な引き戻しは同値。 -/
@[kerodon 01HJ]
lemma IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
    {E B F : SSet.{u}} [Quasicategory E] [Quasicategory B] [Quasicategory F]
    {e : E ⟶ B} (he : IsQCatEquivalence e) (p : F ⟶ B)
    (hp : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting p) : IsPrecompositionEquivalence (pullback.snd e p) := by
  letI : InnerFibration p := SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.innerFibration hp
  letI : TrivialKanFibration (relativeEquivalencePathMapAt p 1) :=
    F1B.kanRelativeEquivalencePathMapAt_one_trivialKanFibration p
      (SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.invertibleTargetLifting hp)
  exact (he.pullback_snd_of_relativePath p).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
