module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoIdentityFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyConstantComponent

/-!
概要：元の恒等比較の curry は、元の curry した関手の恒等比較である。
方針：元の関手空間の curry 作用と、その恒等保存を使う。
規約：指定同型の値を保持。使われ方：普遍輸送の恒等係数の余分な比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の関手の恒等比較を curry すると、同じ curry した関手の恒等比較となる。 -/
lemma functorIso_curry_refl {A B X : SSet.{u}} [Quasicategory X] (f : A ⊗ B ⟶ X) :
    FunctorIso.curry (f := f) (g := f)
      (Iso.refl (SSet.HomotopyCategory.mk (functorVertex f))) =
      Iso.refl (SSet.HomotopyCategory.mk (functorVertex (curry f))) := by
  let e : FunctorIso f f := Iso.refl (SSet.HomotopyCategory.mk (functorVertex f))
  have hm := vertexIso_map_heq_refl_of_heq e rfl (HEq.rfl) (functorSpaceCurryMap A B X)
  exact eq_of_heq ((functorIso_curry_heq_map e).trans
    (hm.trans (iso_refl_heq_of_eq
      (congrArg SSet.HomotopyCategory.mk (functorSpaceCurryMap_vertex f)))))

end SerrePositivity.InfinityCategories.F2
