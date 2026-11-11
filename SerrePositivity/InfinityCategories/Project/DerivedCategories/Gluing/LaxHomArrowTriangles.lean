module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomArrowInterval
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowHomTriangleCurry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowHomTriangleFaces

/-! 元の lax 写像空間比較の矢印側を、同じ augmentation を固定した二合成三角形へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomArrowTriangles (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y)

lemma dgGluingLaxHomArrowTriangles_recover (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomIntervalOfTriangles (dgGluingLaxHomArrowTriangles R C D M X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTriangleEquiv.left_inv _

lemma dgGluingLaxHomArrowTriangles_source (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).first =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M X :=
  (dgGluingLaxHomArrowTriangles R C D M X Y).source

lemma dgGluingLaxHomArrowTriangles_target (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).second =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationArrowDiagram R C D M Y :=
  (dgGluingLaxHomArrowTriangles R C D M X Y).target

lemma dgGluingLaxHomArrowTriangles_diagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).first =
      (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ (dgGluingLaxHomArrowTriangles R C D M X Y).second :=
  (dgGluingLaxHomArrowTriangles R C D M X Y).diagonal

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
