module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowTriangles

/-! 元の lax 比較の二合成三角形の残る二辺を、同じ実成分評価として回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomArrowComponent (X Y : DGGluingObject R C D M) (i : Fin 2) :=
  dgGluingLaxHomArrowIntervalComparison R C D M X Y ≫
    intervalMappingPostOfEq (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i))
      (functorVertex (dgGluingDerivedAugmentationArrowDiagram R C D M X))
      (functorVertex (dgGluingDerivedAugmentationArrowDiagram R C D M Y))
      (evaluateFunctorAt_functorVertex _ (dgGluingDerivedAugmentationArrowDiagram R C D M X))
      (evaluateFunctorAt_functorVertex _ (dgGluingDerivedAugmentationArrowDiagram R C D M Y))

lemma dgGluingLaxHomArrowTriangles_first_last (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).first =
      intervalMappingUncurry (dgGluingLaxHomArrowComponent R C D M X Y 1) :=
  dgGluingArrowHomTriangle_first_last _

lemma dgGluingLaxHomArrowTriangles_second_first (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).second =
      intervalMappingUncurry (dgGluingLaxHomArrowComponent R C D M X Y 0) :=
  dgGluingArrowHomTriangle_second_first _

end SerrePositivity.InfinityCategories
