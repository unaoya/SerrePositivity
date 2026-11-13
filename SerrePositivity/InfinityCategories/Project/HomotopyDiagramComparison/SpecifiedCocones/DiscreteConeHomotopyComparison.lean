module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeComparisonReflection
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の離散錐の脚ごとのホモトピーを、元の極限・Bousfield–Kan 比較のホモトピーにする。
方針：同じ円柱を元の離散積へ持ち上げ、標準比較の厳密な因子化を後合成する。
規約：元の頂点・脚・比較射を保持。Kan 性は構成には不要。
使われ方：元の有限評価錐の極限性を、脚の Kan ホモトピーから検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の離散図式と固定頂点からの元の全脚を持つ通常の錐。 -/
def discreteConeOfLegs {J : Type u} (D : Discrete J ⥤ SSet.{u}) (A : SSet.{u})
    (f : (i : Discrete J) → A ⟶ D.obj i) : Cone D where
  pt := A
  π := Discrete.natTrans f

/-- 元の全脚の円柱を元の離散極限に持ち上げた、元の二つの普遍射のホモトピー。 -/
def discreteLimitLiftHomotopy {J : Type u} (D : Discrete J ⥤ SSet.{u}) (A : SSet.{u})
    {f g : (i : Discrete J) → A ⟶ D.obj i} (H : ∀ i, SSet.Homotopy (f i) (g i)) :
    SSet.Homotopy (limit.lift D (discreteConeOfLegs D A f))
      (limit.lift D (discreteConeOfLegs D A g)) where
  h := limit.lift D (discreteConeOfLegs D (A ⊗ (Δ[1] : SSet.{u})) (fun i ↦ (H i).h))
  h₀ := by
    change SSet.ι₀ ≫ limit.lift D (discreteConeOfLegs D (A ⊗ (Δ[1] : SSet.{u}))
      (fun i ↦ (H i).h)) = limit.lift D (discreteConeOfLegs D A f)
    apply limit.hom_ext
    intro i
    rw [Category.assoc, limit.lift_π, limit.lift_π]
    exact (H i).h₀
  h₁ := by
    change SSet.ι₁ ≫ limit.lift D (discreteConeOfLegs D (A ⊗ (Δ[1] : SSet.{u}))
      (fun i ↦ (H i).h)) = limit.lift D (discreteConeOfLegs D A g)
    apply limit.hom_ext
    intro i
    rw [Category.assoc, limit.lift_π, limit.lift_π]
    exact (H i).h₁
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 元の全脚の円柱から、元の二つの Bousfield–Kan 比較のホモトピーを構成する。 -/
def discreteHolimComparisonHomotopy {J : Type u} (D : Discrete J ⥤ SSet.{u}) (A : SSet.{u})
    {f g : (i : Discrete J) → A ⟶ D.obj i} (H : ∀ i, SSet.Homotopy (f i) (g i)) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (discreteConeOfLegs D A f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (discreteConeOfLegs D A g)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_limitLift, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_limitLift]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (discreteLimitLiftHomotopy D A (f := f) (g := g) H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison D)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
