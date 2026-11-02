module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTriangles
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitCoconeTriangle

/-!
概要：元の余極限三角形を同じ定値図式の三角形として保持する。
方針：元の余極限関手と定値図式関手で全二単体を写し、元の指定三辺を回収する。
規約：三角形も三辺も再選択しない。使われ方：最初の単位三単体の第零面。
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
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の指定余極限辺の定値図式への同じ持ち上げは、元の二関手の全像を curry する。 -/
lemma coherentColimitConstantHomotopy_curry (H : SSet.Homotopy F G) :
    curry (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H)).h =
      curry H.h ≫ coherentColimitFunctor B ≫
        constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} := by
  change curry (uncurry (SSet.yonedaEquiv.symm (coherentColimitConstantEdge B H).edge)) = _
  rw [curry_uncurry]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
  rfl

/-- 元の余極限二単体を定値図式として表示した同じ指定合成三角形。 -/
def coherentColimitConstantTriangle : FunctorCompositionTriangle
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B l))
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B r))
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B d)) where
  diagram := T.diagram ≫ coherentColimitFunctor B ≫
    constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}
  face_zero := by
    rw [← Category.assoc, T.face_zero, coherentColimitConstantHomotopy_curry]
  face_one := by
    rw [← Category.assoc, T.face_one, coherentColimitConstantHomotopy_curry]
  face_two := by
    rw [← Category.assoc, T.face_two, coherentColimitConstantHomotopy_curry]

end SerrePositivity.InfinityCategories.F2
