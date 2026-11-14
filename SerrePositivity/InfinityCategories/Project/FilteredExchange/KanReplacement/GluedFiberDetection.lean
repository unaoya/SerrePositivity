module
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits


/-!
分割で生成：docstring を書き直すこと
概要：共通部分で底が一致する二つの有限図式を、底の円柱を保って同時に輸送する。
方針：底の図式を有限 pushout から延長し、一つの収縮の二つの制限を持ち上げる。
規約：共通部分の射に単射性を要求しない。
使われ方：積比較の単射側で、有限因子分解の共通境界を保つ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：有限 pushout は有限。
方針：有限余極限の一般補題を span に適用する。
規約：三つの対象は有限。使われ方：共通境界を貼った底の図式の収縮。 -/
lemma finite_pushout {A K L : SSet.{u}} [A.Finite] [K.Finite] [L.Finite]
    (i : A ⟶ K) (j : A ⟶ L) : (pushout i j).Finite := by
  apply SSet.finite_of_isColimit (pushoutIsPushout i j)
  rintro (_ | _ | _) <;> dsimp <;> infer_instance

end SerrePositivity.InfinityCategories.Project.FilteredExchange
