module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEnrichedFunctor

/-!
概要：元の豊穣関手の合成と Hom の core を取る操作は厳密に可換。
方針：同じ対象と各 Hom における core 関手の合成保存を使う。
規約：全対象・全高次に関する豊穣関手の等式。
使われ方：二重底変換の実現を元の二つの ∞ 関手の合成へ正規化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w z
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の豊穣関手の合成を core へ移すと、同じ二つの core 上の関手の合成になる。 -/
lemma quasicategoryCoreEnrichedFunctor_comp {C : Type v} {D : Type w} {E : Type z}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D] [EnrichedCategory SSet.{u} E]
    (F : EnrichedFunctor SSet.{u} C D) (G : EnrichedFunctor SSet.{u} D E) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor (F.comp SSet G) =
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor F).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor G) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp (F.map X Y) (G.map (F.obj X) (F.obj Y))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
