module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.WeightedColimitDegree

/-!
概要：coend の単体からの集合の写像は各生成元上で比較できる。
方針：評価した cowedge の余極限の外延性を使う。
規約：比較する写像に単体方向の自然性を要求しない。
使われ方：標準比較の各次数での両逆則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：各次数の coend からの写像は普遍脚上の値で決まる。
方針：集合の射として cowedge の外延性を使う。
規約：T は任意の同じ宇宙の型。使われ方：全単射の検証。 -/
lemma weightedColimitDegree_hom_ext {I : Type u} [SmallCategory I]
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
    {T : Type u} {f g : (weightedColimit W F).obj d → T}
    (h : ∀ i x, f ((weightedColimitι W F i).app d x) =
      g ((weightedColimitι W F i).app d x)) : f = g := by
  have he : (↾f : (weightedColimit W F).obj d ⟶ T) = ↾g := by
    apply Cowedge.IsColimit.hom_ext (weightedColimitDegreeCowedge_isColimit W F d)
    intro i
    apply ConcreteCategory.hom_ext
    exact h i
  funext x
  exact ConcreteCategory.congr_hom he x

/-- 概要：通常の余極限の各次数からの写像も全ての脚で比較できる。
方針：評価関手が保存する余極限の外延性を使う。
規約：filtered 性は不要。使われ方：Over 図式の余極限上の逆則。 -/
lemma colimitDegree_hom_ext {I : Type u} [SmallCategory I]
    (F : I ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
    {T : Type u} {f g : (colimit F).obj d → T}
    (h : ∀ i x, f ((colimit.ι F i).app d x) = g ((colimit.ι F i).app d x)) : f = g := by
  have hc := isColimitOfPreserves ((evaluation _ _).obj d) (colimit.isColimit F)
  have he : (↾f : (colimit F).obj d ⟶ T) = ↾g := by
    apply hc.hom_ext
    intro i
    apply ConcreteCategory.hom_ext
    exact h i
  funext x
  exact ConcreteCategory.congr_hom he x

end SerrePositivity.InfinityCategories.F2
