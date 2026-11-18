module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
概要：終点の付加と AsSmall の順序を変える、同じ全単体の添字同型を示す。
方針：既存の WithTerminal.map を AsSmall.up・down に適用し、両逆を各枝で計算する。
規約：HTT 1.2.8、Kerodon §4.3.5（Tag 017V）の既存の join と nerve の宇宙移送の法則。
使われ方：有限被覆の指定全錐を、係数と同じ宇宙の終点付き添字へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
variable (I : Type u) [SmallCategory I]

/-- AsSmall を経由して戻る終点付き関手は恒等関手。 -/
lemma withTerminal_asSmall_up_down :
    WithTerminal.map (AsSmall.up : I ⥤ AsSmall.{u + 1} I) ⋙
      WithTerminal.map (AsSmall.down : AsSmall.{u + 1} I ⥤ I) = 𝟭 (WithTerminal I) := by
  refine CategoryTheory.Functor.ext (fun X => by cases X <;> rfl) ?_
  intro X Y f
  cases X <;> cases Y
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · rfl
  · exact (WithTerminal.false_of_from_star f).elim
  · rfl

/-- 逆順の二つの終点付き関手も恒等関手。 -/
lemma withTerminal_asSmall_down_up :
    WithTerminal.map (AsSmall.down : AsSmall.{u + 1} I ⥤ I) ⋙
      WithTerminal.map (AsSmall.up : I ⥤ AsSmall.{u + 1} I) =
        𝟭 (WithTerminal (AsSmall.{u + 1} I)) := by
  refine CategoryTheory.Functor.ext (fun X => by cases X <;> rfl) ?_
  intro X Y f
  cases X <;> cases Y
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · rfl
  · exact (WithTerminal.false_of_from_star f).elim
  · rfl

/-- 元の全単体を保つ、終点と宇宙移送の同じ添字同型。 -/
def nerveWithTerminalAsSmallIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (WithTerminal I)) ≅
      nerve (WithTerminal (AsSmall.{u + 1} I)) where
  hom :=
    { app _ := ↾fun s => s.down ⋙ WithTerminal.map (AsSmall.up : I ⥤ AsSmall.{u + 1} I)
      naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun s => ULift.up (s ⋙ WithTerminal.map (AsSmall.down : AsSmall.{u + 1} I ⥤ I))
      naturality _ _ _ := rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change ULift.up ((s.down ⋙ WithTerminal.map (AsSmall.up : I ⥤ AsSmall.{u + 1} I)) ⋙
      WithTerminal.map (AsSmall.down : AsSmall.{u + 1} I ⥤ I)) = s
    rw [CategoryTheory.Functor.assoc, withTerminal_asSmall_up_down,
      CategoryTheory.Functor.comp_id]
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (s ⋙ WithTerminal.map (AsSmall.down : AsSmall.{u + 1} I ⥤ I)) ⋙
      WithTerminal.map (AsSmall.up : I ⥤ AsSmall.{u + 1} I) = s
    rw [CategoryTheory.Functor.assoc, withTerminal_asSmall_down_up,
      CategoryTheory.Functor.comp_id]

/-- 同じ添字同型は元の脚の包含と可換。 -/
lemma nerveWithTerminalAsSmallIso_incl :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I)) ≫
      (nerveWithTerminalAsSmallIso I).hom =
        (nerveAsSmallIso I).hom ≫
          nerveMap (WithTerminal.incl : AsSmall.{u + 1} I ⥤ WithTerminal (AsSmall.{u + 1} I)) := rfl

/-- 終点の頂点は、同じ元の終点の持ち上げに戻る。 -/
lemma nerveWithTerminalAsSmallIso_star :
    (nerveWithTerminalAsSmallIso I).inv.app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (WithTerminal.star : WithTerminal (AsSmall.{u + 1} I))) =
        ULift.up (ComposableArrows.mk₀ (WithTerminal.star : WithTerminal I)) := by
  apply ULift.ext
  apply ComposableArrows.ext₀
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
