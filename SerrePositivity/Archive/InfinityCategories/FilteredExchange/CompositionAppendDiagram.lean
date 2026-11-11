module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSliceAppendEdge
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionPrism

/-!
概要：元の二つの Hom の合成 prism と同じ最終射を、一つの実高次図式へ束ねる。
方針：元の全錐に射を追加する実 slice 写像を展開する。
規約：全係数・元の指定射・実終辺を保持。使われ方：三射の実四面体族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二 Hom の合成 prism に、同じ最後の射を付け足した実高次図式。 -/
def coherentCompositionAppendDiagram
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W) :
    join (Δ[1] ⊗ ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))) Δ[1] ⟶
        SimplicialNerve C :=
  sliceOverUncurry (coherentCompositionPrism X Y Z ≫ coherentRightSliceAppendEdge g)

/-- 実終辺全体は、同じ元の最終射の coherent な辺に厳密に固定される。 -/
lemma coherentCompositionAppendDiagram_fixed
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W) :
    joinInr _ Δ[1] ≫ coherentCompositionAppendDiagram X Y Z W g =
      SSet.yonedaEquiv.symm (coherentNerveEdge g).edge :=
  sliceOverUncurry_fixed _

end SerrePositivity.InfinityCategories.F2
