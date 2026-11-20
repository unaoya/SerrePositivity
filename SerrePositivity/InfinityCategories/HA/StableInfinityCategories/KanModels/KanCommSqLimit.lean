module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity

/-!
分割で生成：docstring を書き直すこと
 # 元の Kan homotopy pullback 四角形を、同じ全 coherent 極限錐へ移す
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels
open _root_.SerrePositivity.KST.Fibration

/-- 元の通常射の anodyne–fibration 分解の中間値は、同じ実 Kan 対象である。 -/
def kanCommSqReplacementTarget {Y Z : SSet.{u}} [KanComplex Z] (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := by
  let W := AnodyneKanReplacement.factorization.Z.obj (Arrow.mk g)
  let p : W ⟶ Z := AnodyneKanReplacement.factorization.p.app (Arrow.mk g)
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr
    (AnodyneKanReplacement.factorization.hp _)
  refine ⟨W, ?_⟩
  change Fibration (terminal.from W)
  rw [show terminal.from W = p ≫ terminal.from Z from terminal.hom_ext _ _]
  infer_instance

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
