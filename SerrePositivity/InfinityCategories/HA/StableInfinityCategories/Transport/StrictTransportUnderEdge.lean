module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
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
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveUnderMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCocones

/-!
分割で生成：docstring を書き直すこと
 # strict transport の元の undercategory 内の恒等射からの辺
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport
open _root_.SerrePositivity.KST.Fibration

/-- 元の undercategory で、恒等射から入力された射へ向かう実辺。 -/
def strictTransportUnderEdge {I : Type u} [Category.{u} I] {c d : I} (f : c ⟶ d) :
    (Δ[1] : SSet.{u}) ⟶ nerve (Under c) :=
  yonedaEquiv.symm (nerve.edgeMk (Under.homMk f (by simp) :
    Under.mk (𝟙 c) ⟶ Under.mk f)).edge

/-- 底の射は、元の入力射そのもの。 -/
theorem strictTransportUnderEdge_projection {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge f ≫ nerveMap (Under.forget c) =
      yonedaEquiv.symm (nerve.edgeMk f).edge := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rw [nerve.edgeMk_edge, nerve.edgeMk_edge, nerveMap_app_mk₁]
  rfl

/-- strict transport の前合成は、元の終点の恒等射を入力射へ送る。 -/
theorem kanCocartesianUnderMap_identity_vertex {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex, nerveMap_app_mk₀]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (f ≫ 𝟙 d)) = _
  rw [Category.comp_id]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanCocartesianUnderMap_identity_vertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.kanCocartesianUnderMap_identity_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportUnderEdge := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportUnderEdge_projection := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportUnderEdge._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportUnderEdge.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge.eq_1
