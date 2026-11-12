module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramOrdinaryFunctor
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：二つの元の豊穣図式比較を、同じ三辺を持つ三点と底の積上の図式へ束ねる。
方針：元の自然変換の二射の列を uncurry し、長辺を同じ比較成分の合成とする。
規約：底全体と元の全高次 Hom に同時に自然なまま実現に渡す。
使われ方：底変換比較の合成則の coherent な二単体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] {D E F : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
  (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E) (θ : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison E F)

/-- 同じ二比較とその成分の合成を三辺に持つ、三点と底全体の豊穣図式。 -/
def quasicategoryEnrichedDiagramTriangle : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C (Fin 3 × J) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram.ofFunctor
    (Functor.uncurry.obj (ComposableArrows.mk₂ η.toNatTrans θ.toNatTrans))

/-- 三角形の最初の辺は、元の最初の比較の同じ成分。 -/
lemma quasicategoryEnrichedDiagramTriangle_first (a : J) (X : C) :
    ((quasicategoryEnrichedDiagramTriangle η θ).map
      ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) : ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a))).val X =
      (η.app a).val X := by
  change (η.app a).val X ≫ (E.map (𝟙 a)).val X = _
  rw [E.map_id]
  exact Category.comp_id ((η.app a).val X)

/-- 三角形の次の辺は、元の次の比較の同じ成分。 -/
lemma quasicategoryEnrichedDiagramTriangle_second (a : J) (X : C) :
    ((quasicategoryEnrichedDiagramTriangle η θ).map
      ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) : ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a))).val X =
      (θ.app a).val X := by
  change (θ.app a).val X ≫ (F.map (𝟙 a)).val X = _
  rw [F.map_id]
  exact Category.comp_id _

/-- 三角形の長辺は、元の二つの比較成分そのものの合成。 -/
lemma quasicategoryEnrichedDiagramTriangle_long (a : J) (X : C) :
    ((quasicategoryEnrichedDiagramTriangle η θ).map
      ((homOfLE (show (0 : Fin 3) ≤ 2 by decide), 𝟙 a) : ((0 : Fin 3), a) ⟶ ((2 : Fin 3), a))).val X =
      (η.app a).val X ≫ (θ.app a).val X := by
  change ((η.app a).val X ≫ (θ.app a).val X) ≫ (F.map (𝟙 a)).val X = _
  rw [F.map_id]
  exact Category.comp_id _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
