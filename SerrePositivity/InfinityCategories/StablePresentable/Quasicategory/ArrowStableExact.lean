module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
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
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.TerminalMap
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullback
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackExactProjections
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLift
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackProjections
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackStable
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationSquares
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationStability

/-!
分割で生成：docstring を書き直すこと
概要：安定圏の矢印圏の安定性と、両端による完全性の判定。
方針：恒等二関手の lax pullback との厳密同型で元の F2 の完全射影を輸送する。
規約：元の内部 Hom の全単体を使う。使われ方：cofiber 回転による差の関手の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable (X : SSet.{u})

def arrowLaxInverse : (ihom (Δ[1] : SSet.{u})).obj X ⟶ F2.laxPullback (𝟙 X) (𝟙 X) :=
  F2.laxPullbackLift (𝟙 X) (𝟙 X)
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) (𝟙 _)
    (by simp) (by simp)

lemma arrowLaxInverse_fst : arrowLaxInverse X ≫ F2.laxPullbackFst (𝟙 X) (𝟙 X) =
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := F2.laxPullbackLift_fst ..

lemma arrowLaxInverse_snd : arrowLaxInverse X ≫ F2.laxPullbackSnd (𝟙 X) (𝟙 X) =
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := F2.laxPullbackLift_snd ..

lemma arrowLaxInverse_arrow : arrowLaxInverse X ≫ F2.laxPullbackArrow (𝟙 X) (𝟙 X) =
    𝟙 ((ihom (Δ[1] : SSet.{u})).obj X) := F2.laxPullbackLift_arrow ..

def arrowLaxIso : F2.laxPullback (𝟙 X) (𝟙 X) ≅ (ihom (Δ[1] : SSet.{u})).obj X where
  hom := F2.laxPullbackArrow (𝟙 X) (𝟙 X)
  inv := arrowLaxInverse X
  hom_inv_id := by
    apply F2.laxPullback_hom_ext
    · rw [Category.assoc, arrowLaxInverse_arrow, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, arrowLaxInverse_fst, F2.laxPullbackArrow_source,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, arrowLaxInverse_snd, F2.laxPullbackArrow_target,
        Category.comp_id, Category.id_comp]
  inv_hom_id := F2.laxPullbackLift_arrow ..

variable [Quasicategory X] [IsStable X]

instance arrow_isStable : IsStable ((ihom (Δ[1] : SSet.{u})).obj X) :=
  isStable_of_trivialKanFibration (arrowLaxIso X).inv

instance arrow_source_isExact : IsExactFunctor
    (evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  rw [← arrowLaxInverse_fst]
  have : IsExactFunctor (arrowLaxInverse X) :=
    inferInstanceAs (IsExactFunctor (arrowLaxIso X).inv)
  infer_instance

instance arrow_target_isExact : IsExactFunctor
    (evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  rw [← arrowLaxInverse_snd]
  have : IsExactFunctor (arrowLaxInverse X) :=
    inferInstanceAs (IsExactFunctor (arrowLaxIso X).inv)
  infer_instance

end SerrePositivity.KST.LocalizingInvariants
