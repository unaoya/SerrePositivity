module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.WeightedColimitFamilies
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：重み付き脚上の dinatural なホモトピーを coend 全体のホモトピーへ貼る。
方針：円柱をパラメータ付き coend の普遍性で降下させ、両端を脚で比較する。
規約：標的の Kan 性や quasicategory 性は不要。
使われ方：Bousfield–Kan coend の terminal な添字での収縮。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：脚上で指定した dinatural なホモトピーを coend 全体へ貼り合わせる。
方針：円柱の降下の両端を coend の普遍脚で検証する。
規約：指定された射 f,g をそのまま両端にする。使われ方：augmentation の収縮の検証。 -/
def weightedColimitHomotopy {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}} {Y : SSet.{u}}
    {f g : weightedColimit W F ⟶ Y}
    (d : ∀ i, SSet.Homotopy (weightedColimitι W F i ≫ f) (weightedColimitι W F i ≫ g))
    (hd : ∀ {i j} (a : i ⟶ j),
      ((F.obj i ◁ W.map a.op) ▷ (Δ[1] : SSet.{u})) ≫ (d i).h =
        ((F.map a ▷ W.obj (Opposite.op j)) ▷ (Δ[1] : SSet.{u})) ≫ (d j).h) :
    SSet.Homotopy f g where
  h := weightedColimitFamily W F Δ[1] Y (fun i ↦ (d i).h) hd
  h₀ := by
    change SSet.ι₀ ≫ weightedColimitFamily W F Δ[1] Y (fun i ↦ (d i).h) hd = f
    apply weightedColimit_hom_ext
    intro i
    rw [← SSet.ι₀_comp_assoc, weightedColimitι_family, (d i).h₀]
  h₁ := by
    change SSet.ι₁ ≫ weightedColimitFamily W F Δ[1] Y (fun i ↦ (d i).h) hd = g
    apply weightedColimit_hom_ext
    intro i
    rw [← SSet.ι₁_comp_assoc, weightedColimitι_family, (d i).h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.F2
