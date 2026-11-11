module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：底の指定収縮を、指定図式に厳密に一致する制限として読む。
方針：全円柱を前合成し、始点だけ指定の等式で表示し直す。
規約：元の制限円柱を全単体で保持する。
使われ方：二入力の輸送と標的の相対輸送に同じ底の円柱を使う。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-- 概要：指定された底の収縮を指定した始点射への収縮として制限する。
方針：円柱の前合成と端点の自然性を使う。
規約：h は元の全円柱の前合成そのもの。使われ方：両端の底上の同時輸送。 -/
def nullHomotopyRestriction {A M B : SSet.{u}} {r : M ⟶ B} {f : A ⟶ B}
    {b : B _⦋0⦌} (H : SSet.Homotopy r (SSet.const b)) (i : A ⟶ M) (hi : i ≫ r = f) :
    SSet.Homotopy f (SSet.const b) where
  h := (i ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact hi
  h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
  rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i).rel

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
