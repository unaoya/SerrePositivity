module
public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.SuspensionExactNaturality

public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberExactNaturality

/-!
概要：選んだ全単体上の suspension は任意の完全関手と関手同型で可換する。
方針：cofiber の完全関手に関する比較と零終点矢印の始点評価を合成する。
規約：h 圏だけの可換性に弱めない。使われ方：商関手の後の shift の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]

def exactNaturality : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X ≫ F) (F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map Y) := by
  let b := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X ≫ F) (b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Y (𝟙 _)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map, b, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (CofiberFamily.exactNaturality F) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X)
  have e := (CofiberFamily.compositionIso Y b).symm ≪≫
    cofiberZeroTargetIso Y b (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.post_arrow_zero_target F)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.post_arrow_source] at e
  exact h ≪≫ e

end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
