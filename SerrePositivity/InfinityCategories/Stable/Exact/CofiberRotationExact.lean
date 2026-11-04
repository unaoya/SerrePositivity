module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationSquares

/-!
分割で生成：docstring を書き直すこと
概要：安定圏の cofiber の元の全単体上の選択は完全関手。
方針：底辺と右辺の評価の trivial Kan fibration 性から cofiber 回転の完全性を得る。
規約：元の選択された cofiber 関手を変更しない。使われ方：差の実関手の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 自明 Kan fibration との合成の完全性から元の関手の完全性を戻す。 -/
lemma exact_of_postcomp_trivialKanFibration {A B C : SSet.{u}}
    [Quasicategory B] [Quasicategory C] (q : B ⟶ C) [TrivialKanFibration q]
    (F : A ⟶ B) [IsExactFunctor (F ≫ q)] : IsExactFunctor F where
  preservesZero x hx := (isZeroVertex_iff_map_of_trivialKanFibration q _).2
    (IsExactFunctor.preservesZero (F := F ≫ q) x hx)
  preservesCofiber t ht :=
    (isPushoutSquare_iff_postcomp_trivialKanFibration q (t.square ≫ F)).2
      (IsExactFunctor.preservesCofiber (F := F ≫ q) t ht)

end SerrePositivity.KST.LocalizingInvariants
