module

public import SerrePositivity.InfinityCategories.Sheaves.CechShape
public import SerrePositivity.InfinityCategories.Sheaves.CechCofinalityModel
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite

/-!
概要：元の Čech 形状と大きい site の Čech 形状の left cofinality。
方針：同じ図式の小さい模型での Quillen A を、矢の厳密な同型で戻す。
使われ方：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）。
規約：小さい site と大きい site とも、元の指定形状の cofinality を結論する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 対象・射の宇宙が違う圏でも、その共通の宇宙で nerve と AsSmall の nerve は同型。 -/
def nerveAsSmallMaxIso (D : Type u) [Category.{v} D] :
    nerve D ≅ nerve (AsSmall.{max u v} D) where
  hom :=
    { app := fun _ ↦ ↾fun s ↦ s ⋙ AsSmall.up
      naturality := fun _ _ _ ↦ rfl }
  inv :=
    { app := fun _ ↦ ↾fun s ↦ s ⋙ AsSmall.down
      naturality := fun _ _ _ ↦ rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 小さい site の指定された元の Čech 形状は left cofinal。 -/
lemma cechShape_isLeftCofinal {C : Type u} [SmallCategory C] {U : C}
    (d : CategoryTheory.CechNerveData U) (hU : CategoryTheory.IsWeaklyTerminal U) :
    IsLeftCofinal (cechShape d) := by
  let e : Arrow.mk (cechShape d) ≅
      Arrow.mk (nerveMap (cechSmallFunctor.{u, u, u + 1} d)) :=
    Arrow.isoMk (nerveAsSmallIso.{0, u + 1} SimplexCategory)
      (nerveAsSmallIso.{u, u + 1} Cᵒᵖ) (by rfl)
  exact (cechSmallFunctor_nerve_isLeftCofinal.{u, u, u + 1} d hU).of_arrow_iso e.symm

/-- 大きい site でも、元の小さい Δ からの同じ Čech 形状が left cofinal。 -/
lemma cechShapeLarge_isLeftCofinal {C : Type (u + 1)} [Category.{u} C] {U : C}
    (d : CategoryTheory.CechNerveData U) (hU : CategoryTheory.IsWeaklyTerminal U) :
    IsLeftCofinal (cechShapeLarge d) := by
  let e : Arrow.mk (cechShapeLarge d) ≅
      Arrow.mk (nerveMap (cechSmallFunctor.{u + 1, u, u + 1} d)) :=
    Arrow.isoMk (nerveAsSmallIso.{0, u + 1} SimplexCategory)
      (nerveAsSmallMaxIso Cᵒᵖ) (by rfl)
  exact (cechSmallFunctor_nerve_isLeftCofinal.{u + 1, u, u + 1} d hU).of_arrow_iso e.symm

end SerrePositivity.InfinityCategories.Sheaves
