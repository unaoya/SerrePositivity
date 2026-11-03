module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSliceAppendEdgeCone

/-!
概要：元の全右 slice の錐へ指定射を追加し、その同じ辺上の slice へ束ねる。
方針：実区間全体の固定条件と全添字自然性を使う。
規約：元の全錐・指定射を保持。使われ方：三射の実高次族を展開する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全右 slice へ指定射を追加する、同じ実辺上の slice への実写像。 -/
def coherentRightSliceAppendEdge
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {Z W : C} (g : Z ⟶ W) :
    sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z)) ⟶
      sliceOver (SSet.yonedaEquiv.symm (coherentNerveEdge g).edge) where
  app _ := ↾fun c => ⟨coherentRightSliceAppendEdgeCone g c,
    coherentRightSliceAppendEdgeCone_fixed g c⟩
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    exact (coherentRightSliceAppendEdgeCone_naturality g α.unop c).symm

end SerrePositivity.InfinityCategories.F2
