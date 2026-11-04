module
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedReverseCompositionTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceMappingSpaces
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration

/-!
分割で生成：docstring を書き直すこと
 # Kan 写像の本質的全射性を、同じ点の射の全射性から回収する

実 pointed fiber の同型と、既存の全写像空間の同値による逆像を使う。
高次写像空間の充満忠実性を零次の主張で代用しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 標準の一点 Hom 同型で座標を揃えた、実 pointed fiber への既存比較。 -/
def kanPointFiberComparison (K : KanObject.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj K.obj).op ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex K) :=
  (SSet.opFunctor.mapIso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (pointKanObjectHomIso K))).inv ≫
      pointedReverseKanFiberComparison K

/-- 座標変更後も、同じ比較は全写像空間で充満忠実。 -/
theorem kanPointFiberComparison_isFullyFaithful (K : KanObject.{u}) :
    IsFullyFaithful (kanPointFiberComparison K) :=
  ((qCatEquivalenceOfIso (SSet.opFunctor.mapIso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (pointKanObjectHomIso K))).symm).isQCatEquivalence.comp
      (pointedReverseKanFiberComparison_isQCatEquivalence K)).isFullyFaithful

end SerrePositivity.KST.Fibration
