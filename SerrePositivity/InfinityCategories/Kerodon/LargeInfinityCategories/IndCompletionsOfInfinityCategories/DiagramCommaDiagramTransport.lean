module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaRestrictionLaws
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaOriginalFamilyNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaRightPrism

/-!
概要：元の全図式の等号による comma の表示移送は、C 全族と全円柱を保持する。
方針：元の図式等号を消去する。
規約：新たな同型の選択や余錐の変更を行わない。
使われ方：形状 pushout の同じ共通境界を、両局所図式の表示で照合する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  {D D' : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C} (h : D = D')
  {T : SSet.{u + 1}} (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)
/-- 概要：元の図式の等号移送は同じ C 全族を厳密に保持。
方針：元の等号を消去。規約：全射の等号。使われ方：共有境界の C 成分。 -/
lemma diagramCommaOriginalFamily_transport :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily κ D' (q ≫ eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ) h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily κ D q := by
  subst D'
  simp only [eqToHom_refl, Category.comp_id]
/-- 概要：元の図式の等号移送は同じ全円柱を厳密に保持。
方針：元の等号を消去。規約：全射の等号。使われ方：共有境界の全変換。 -/
lemma diagramCommaRightPrism_transport :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism κ D' (q ≫ eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ) h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism κ D q := by
  subst D'
  simp only [eqToHom_refl, Category.comp_id]
/-- 概要：同じ形状射の等号で、元の制限族は指定図式等号の移送と厳密に可換。
方針：元の形状射の等号を消去。規約：全射の等号。使われ方：pushout の共有境界。 -/
lemma diagramCommaRestriction_congr {J : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    {f g : J ⟶ K} (hfg : f = g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D f ≫ eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ)
      (congrArg (fun a ↦ (SSet.uliftFunctor.{u + 1, u}).map a ≫ D) hfg)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D g := by
  subst g
  simp only [eqToHom_refl, Category.comp_id]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
