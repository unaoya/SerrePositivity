module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTrianglePrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorCospanCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：元の全 cospan 錐と余極限後の全錐を、元の単位の全円柱で同時に結ぶ。
方針：元の全錐をパラメータとし、左右二単体の制限を元の単位三角柱へ揃える。
規約：全錐・共有対角辺・指定三角形を保持。使われ方：a6 の比較との全錐の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F X} {b : SSet.Homotopy F Y}
  {f : SSet.Homotopy X Z} {g : SSet.Homotopy Y Z} {d : SSet.Homotopy F Z}
  (L : FunctorCompositionTriangle a f d) (R : FunctorCompositionTriangle b g d)

/-- 元の全 cospan 錐から、その余極限像の定値図式への同じ単位の全円柱。 -/
def coherentColimitUnitCospanHomotopy :
    SSet.Homotopy (functorCospanCone L R).val
      ((mapJoinCone (coherentColimitFunctor B) (functorCospanCone L R)).val ≫
        constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}) :=
  coherentColimitUnitParameterHomotopy B (functorCospanCone L R).val

/-- 左三角形上では元の左二単体の全単位三角柱を厳密に回収する。 -/
lemma coherentColimitUnitCospanHomotopy_left :
    (cospanConeTriangleLeft ▷ (Δ[1] : SSet.{u + 1})) ≫
      (coherentColimitUnitCospanHomotopy B L R).h =
        coherentColimitUnitTrianglePrism B L := by
  change _ ≫ (((functorCospanCone L R).val ▷ Δ[1]) ≫ coherentColimitUnitFamily B) = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((cospanConeTriangleLeft ≫ functorCospanConeDiagram L R) ▷ Δ[1]) ≫ _ = _
  rw [functorCospanConeDiagram_left]
  rfl

/-- 右三角形上でも同じ全円柱から元の右二単体の全単位三角柱を回収する。 -/
lemma coherentColimitUnitCospanHomotopy_right :
    (cospanConeTriangleRight ▷ (Δ[1] : SSet.{u + 1})) ≫
      (coherentColimitUnitCospanHomotopy B L R).h =
        coherentColimitUnitTrianglePrism B R := by
  change _ ≫ (((functorCospanCone L R).val ▷ Δ[1]) ≫ coherentColimitUnitFamily B) = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((cospanConeTriangleRight ≫ functorCospanConeDiagram L R) ▷ Δ[1]) ≫ _ = _
  rw [functorCospanConeDiagram_right]
  rfl

end SerrePositivity.InfinityCategories.F2
