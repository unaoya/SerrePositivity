module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismPrismSimplexEquality

/-!
概要：元の固定射の全係数 pointed prism と、元の反転合成 prism の制限を一致させる。
方針：実錐の射を標準 join 座標で忠実に検出し、元の全単体の一致を使う。
規約：元の全係数・全単体・実 prism を保持。使われ方：元の指定輸送比較の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の固定射の全 pointed prism は、元の全反転合成 prism の同じ射への制限。 -/
lemma pointedCoherentMorphismPrism_eq_reverse {K L : KanObject.{u}} (f : K ⟶ L) :
    pointedCoherentMorphismPrism f = pointedReverseMorphismPrism f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨p⟩⟩
  apply Subtype.ext
  apply (cancel_epi (leftPointStdSimplexIso n).inv).mp
  apply SSet.yonedaEquiv.injective
  exact (pointedCoherentMorphismPrism_coordinates f t p).trans
    ((pointedMorphismPrism_simplex_eq f t p).symm.trans
      (pointedReverseMorphismPrism_coordinates f t p).symm)

end SerrePositivity.InfinityCategories.F2
