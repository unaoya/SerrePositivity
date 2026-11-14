module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
概要：通常の可算列の反対の添字と標準の塔の添字を厳密に比較する。
方針：AsSmall の持ち上げと忘却を反対と交換し、両向きの関手と nerve の同型を構成する。
規約：添字は AsSmall.{u} ℕ と AsSmall.{u} ℕᵒᵖ。
使われ方：HTT 4.2.4.1、逐次余極限の反変 Hom の塔への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：標準の塔の添字を通常の列の反対の添字へ写す関手。
方針：AsSmall を忘れてから反対の持ち上げを使う。
規約：対象 n は同じ自然数の反対として対応する。
使われ方：反変 Hom の塔を既存の標準添字で扱う。 -/
def oppositeSequenceIndex : AsSmall.{u} ℕᵒᵖ ⥤ (AsSmall.{u} ℕ)ᵒᵖ :=
  AsSmall.down ⋙ AsSmall.up.op

/-- 概要：標準の塔の添字と列の反対の添字の圏同値。
方針：反対の忘却と通常の持ち上げを逆とし、単位・余単位を恒等成分で与える。
規約：通常の極限錐の普遍性を移す際に使う。
使われ方：逐次余極限の全反変 Hom の極限性の再添字。 -/
def oppositeSequenceIndexEquivalence : AsSmall.{u} ℕᵒᵖ ≌ (AsSmall.{u} ℕ)ᵒᵖ where
  functor := oppositeSequenceIndex
  inverse := AsSmall.down.op ⋙ AsSmall.up
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; rfl)

/-- 概要：標準の塔から列の反対への添字関手の nerve は厳密な同型。
方針：逆関手の nerve を逆射とし、射列の対象と射を計算する。
規約：単なる圏同値性より強い nerve の同型性。
使われ方：native な錐の極限性の再添字の仮定を検証する。 -/
instance nerveMap_oppositeSequenceIndex_isIso : IsIso (nerveMap oppositeSequenceIndex.{u}) := by
  let H : (AsSmall.{u} ℕ)ᵒᵖ ⥤ AsSmall.{u} ℕᵒᵖ := AsSmall.down.op ⋙ AsSmall.up
  refine ⟨nerveMap H, ?_, ?_⟩
  all_goals
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
