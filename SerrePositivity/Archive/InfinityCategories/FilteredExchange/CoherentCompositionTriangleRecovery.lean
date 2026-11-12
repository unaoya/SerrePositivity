module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RightPrismUpperRetraction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionTriangle

/-!
概要：元の slice 四角形全体は、その同じ零番三角形の折り畳みから回収できる。
方針：右 join prism の終点側時間の不変性を使う。
規約：四辺の一致へ弱めない。使われ方：元の合成比較を実三角形へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の slice prism の展開全体は、同じ零番三角形から厳密に回収できる。 -/
lemma slicePrismSquare_triangle_recovery {X P : SSet.{u}} (z : X _⦋0⦌)
    (W : (Δ[1] : SSet.{u}) ⊗ P ⟶ sliceOver (SSet.yonedaEquiv.symm z)) :
    transportTriangleParameter P ≫ squarePrismTriangle (slicePrismSquare z W) 0 =
      slicePrismSquare z W := by
  calc
    _ = squareUpperRetraction P ≫ slicePrismSquare z W := by
      rw [← transportTriangleParameter_triangle]
      simp only [squarePrismTriangle, Category.assoc]
    _ = _ := by
      rw [slicePrismSquare, ← Category.assoc, rightMappingSpacePrism_upper_retraction]

/-- 元の coherent 合成四角形全体は、同じ元の合成三角形を畳んだ図式そのもの。 -/
lemma coherentCompositionSquare_triangle_recovery
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C) :
    transportTriangleParameter _ ≫ coherentCompositionTriangle X Y Z =
      coherentCompositionSquare X Y Z :=
  slicePrismSquare_triangle_recovery (coherentNerveVertex Z) (coherentCompositionPrism X Y Z)

end SerrePositivity.InfinityCategories.F2
