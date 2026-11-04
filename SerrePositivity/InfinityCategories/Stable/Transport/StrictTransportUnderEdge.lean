module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.NerveUnderMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCocones

/-!
分割で生成：docstring を書き直すこと
 # strict transport の元の undercategory 内の恒等射からの辺
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の undercategory で、恒等射から入力された射へ向かう実辺。 -/
def strictTransportUnderEdge {I : Type u} [Category.{u} I] {c d : I} (f : c ⟶ d) :
    (Δ[1] : SSet.{u}) ⟶ nerve (Under c) :=
  yonedaEquiv.symm (nerve.edgeMk (Under.homMk f (by simp) :
    Under.mk (𝟙 c) ⟶ Under.mk f)).edge

/-- 底の射は、元の入力射そのもの。 -/
theorem strictTransportUnderEdge_projection {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    strictTransportUnderEdge f ≫ nerveMap (Under.forget c) =
      yonedaEquiv.symm (nerve.edgeMk f).edge := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, strictTransportUnderEdge, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rw [nerve.edgeMk_edge, nerve.edgeMk_edge, nerveMap_app_mk₁]
  rfl

/-- strict transport の前合成は、元の終点の恒等射を入力射へ送る。 -/
theorem kanCocartesianUnderMap_identity_vertex {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    (nerveUnderMap f).app (Opposite.op ⦋0⦌) (nerveVertex (Under.mk (𝟙 d))) =
      nerveVertex (Under.mk f) := by
  rw [nerveUnderMap, nerveVertex, nerveMap_app_mk₀]
  change nerveVertex (Under.mk (f ≫ 𝟙 d)) = _
  rw [Category.comp_id]

end SerrePositivity.KST.Fibration
