module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionInvertibleDetection
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianSections
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianStrictTransport

/-!
分割で生成：docstring を書き直すこと
 # 元の strict transport と両端 fiber 評価を結ぶ全 section 上の実 prism
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Stable.Transport
open SerrePositivity.KST.Fibration

/-- 元の恒等射評価を全空間へ含めると、同じ全 section の恒等射頂点での評価になる。 -/
theorem strictTransportEvaluate_ambient {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) (c : I) :
    SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) =
      cocartesianSectionEvaluate p (nerveMap (Under.forget c)) (nerveVertex (Under.mk (𝟙 c))) := by
  let a := nerveMap (Under.forget c)
  let v := (nerveEquiv (C := Under c)).symm (Under.mk (𝟙 c))
  have hv : v = nerveVertex (Under.mk (𝟙 c)) := ComposableArrows.ext₀ rfl
  have he : SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) =
      cocartesianSectionEvaluate p a v :=
    (Category.assoc _ _ _).trans
      (congrArg (fun m => SerrePositivity.InfinityCategories.cocartesianSectionsι p a ≫ m)
        (SerrePositivity.InfinityCategories.relativeFunctorEvaluate_ι p a v))
  exact he.trans (congrArg (cocartesianSectionEvaluate p a) hv)


end SerrePositivity.InfinityCategories.Stable.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportEvaluate_ambient := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportEvaluate_ambient
