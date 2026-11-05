module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.ZeroTargetArrows
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactFunctor
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.StablePresentable.Exact.ExactArrowMap

/-!
分割で生成：docstring を書き直すこと
概要：選んだ全単体上の suspension は任意の完全関手と関手同型で可換する。
方針：cofiber の完全関手に関する比較と零終点矢印の始点評価を合成する。
規約：h 圏だけの可換性に弱めない。使われ方：商関手の後の shift の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
namespace SerrePositivity.InfinityCategories.StablePresentable.Exact.SuspensionExact
open SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
  [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]

omit [Quasicategory Y] [IsStable Y] in
lemma post_arrow_zero_target (x : X _⦋0⦌) : IsZeroTargetArrow
    ((arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex (((arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) x)
  rw [Category.assoc, arrowMap_evaluation, ← Category.assoc]
  exact IsExactFunctor.preservesZero (F := F) _ (arrow_zero_target X x)

omit [Quasicategory Y] [IsStable Y] [IsExactFunctor F] in
lemma post_arrow_source :
    (arrow X ≫ (ihom (Δ[1] : SSet.{u})).map F) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = F := by
  rw [Category.assoc, arrowMap_evaluation, ← Category.assoc, arrow_source, Category.id_comp]

end SerrePositivity.InfinityCategories.StablePresentable.Exact.SuspensionExact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.post_arrow_source := _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.SuspensionExact.post_arrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.post_arrow_zero_target := _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.SuspensionExact.post_arrow_zero_target
