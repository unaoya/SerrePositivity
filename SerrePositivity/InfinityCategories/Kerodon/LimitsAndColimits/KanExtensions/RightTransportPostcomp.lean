module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：指定右 Kan 変換と局所錐の輸送を、元の標的の射で後合成する。
方針：輸送の円柱全体へ同じ射を合成し、元の端点・図式・頂点の式を保つ。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の降下の局所錐の係数変更。
規約：極限の保存性を仮定せず、指定輸送の法則だけを構成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 右 Kan の標準錐の全射は、標的の後合成と整合する。 -/
lemma kanRightCanonicalCone_postcomp_val {K C D E : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (U : D ⟶ E) (c : C _⦋0⦌) :
    (rightKanCanonicalCone δ (F ≫ U) c).val = (rightKanCanonicalCone δ F c).val ≫ U :=
  (Category.assoc _ _ _).symm

/-- 元の指定余単位の円柱へ後合成し、始端を δ ≫ (F ≫ U) に揃える。 -/
def kanRightCounitPostcomp {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} (α : SSet.Homotopy (δ ≫ F) F₀) (U : D ⟶ E) :
    SSet.Homotopy (δ ≫ (F ≫ U)) (F₀ ≫ U) where
  h := (SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp α U).h
  h₀ := (SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp α U).h₀.trans
    (Category.assoc δ F U)
  h₁ := (SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp α U).h₁
  rel := (SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp α U).rel

/-- 局所輸送の円柱全体を写す。元の図式と頂点の固定式を保持する。 -/
def kanRightTransportPostcomp {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) (U : D ⟶ E) :
    RightKanConeTransport δ (F₀ ≫ U) (F ≫ U) (kanRightCounitPostcomp α U) c where
  family := t.family ≫ U
  start := by rw [← Category.assoc, t.start, kanRightCanonicalCone_postcomp_val]
  diagram := by
    rw [← Category.assoc, t.diagram]
    simp only [Category.assoc]
    rfl
  fixedVertex := by
    rw [← Category.assoc, t.fixedVertex, kanRightCanonicalCone_postcomp_val]
    simp only [Category.assoc]

/-- 後合成した局所輸送の指定錐は、元の指定錐の同じ後合成である。 -/
lemma kanRightTransportPostcomp_cone_val {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) (U : D ⟶ E) :
    (kanRightTransportPostcomp t U).cone.val = t.cone.val ≫ U :=
  (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
