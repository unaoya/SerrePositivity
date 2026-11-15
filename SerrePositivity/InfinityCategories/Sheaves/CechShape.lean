module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import SerrePositivity.CategoryTheory.CechNerveData

/-!
概要：弱終対象のČech脈体を、前層を制限する指定形状として読む。
方針：一般のCechNerveDataの単体的対象のrightOpをnerveへ送る。
使われ方：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の極限の再添字。
規約：Čech側はΔ。大きいsiteでもČech側のサイズを上げない。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Sheaves

abbrev IsWeaklyTerminal {D : Type u} [SmallCategory D] (U : D) : Prop :=
  CategoryTheory.IsWeaklyTerminal U

abbrev CechNerveData {D : Type u} [SmallCategory D] (U : D) :=
  CategoryTheory.CechNerveData U

/-- 元の単体的対象を反対にして、同じΔから前層の添字へ送る。 -/
def cechShape {D : Type u} [SmallCategory D] {U : D} (d : CechNerveData U) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ presheafShape D where
  app _ := ↾fun s => ⟨s.down ⋙ d.obj.rightOp⟩
  naturality _ _ _ := rfl

/-- 大きいsiteでも元の小さい単体圏を保つ同じ指定形状。 -/
def cechShapeLarge {D : Type (u+1)} [Category.{u} D] {U : D}
    (d : CategoryTheory.CechNerveData U) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve Dᵒᵖ where
  app _ := ↾fun s => s.down ⋙ d.obj.rightOp
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Sheaves
