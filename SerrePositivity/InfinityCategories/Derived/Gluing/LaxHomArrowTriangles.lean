module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowInterval
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTriangleCurry
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTriangleFaces

/-! 元の lax 写像空間比較の矢印側を、同じ augmentation を固定した二合成三角形へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomArrowTriangles (X Y : DGGluingObject R C D M) :=
  dgGluingArrowHomTrianglePairOfInterval
    (dgGluingDerivedAugmentationArrowDiagram R C D M X)
    (dgGluingDerivedAugmentationArrowDiagram R C D M Y)
    (dgGluingLaxHomArrowIntervalComparison R C D M X Y)

lemma dgGluingLaxHomArrowTriangles_recover (X Y : DGGluingObject R C D M) :
    dgGluingArrowHomIntervalOfTriangles (dgGluingLaxHomArrowTriangles R C D M X Y) =
      dgGluingLaxHomArrowIntervalComparison R C D M X Y :=
  dgGluingArrowHomTriangleEquiv.left_inv _

lemma dgGluingLaxHomArrowTriangles_source (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).first =
      fst _ _ ≫ dgGluingDerivedAugmentationArrowDiagram R C D M X :=
  (dgGluingLaxHomArrowTriangles R C D M X Y).source

lemma dgGluingLaxHomArrowTriangles_target (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).second =
      fst _ _ ≫ dgGluingDerivedAugmentationArrowDiagram R C D M Y :=
  (dgGluingLaxHomArrowTriangles R C D M X Y).target

lemma dgGluingLaxHomArrowTriangles_diagonal (X Y : DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).first =
      (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).second :=
  (dgGluingLaxHomArrowTriangles R C D M X Y).diagonal

end SerrePositivity.InfinityCategories
