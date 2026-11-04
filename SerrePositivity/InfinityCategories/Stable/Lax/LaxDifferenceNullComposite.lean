module
public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.SquareHomotopyCategory
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamilyZeroTriangle

/-!
分割で生成：docstring を書き直すこと
概要：元の lax 矢印と元の cofiber 射の合成は h Fun で零である。
方針：関手圏内の零角四角形の二辺を元の二つの代表に端点ごと比較する。
規約：各対象での零性ではなく自然変換全体の等式。使われ方：実随伴単位の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 端点も含む二辺の表示変更は、合成の零性を保つ。 -/
lemma comp_zero_of_arrowMk_eq {T : Type*} [Category T] [HasZeroMorphisms T]
    {x y z x' y' z' : T} (f : x ⟶ y) (g : y ⟶ z) (f' : x' ⟶ y') (g' : y' ⟶ z')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g')
    (h : f ≫ g = 0) : f' ≫ g' = 0 := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  obtain ⟨_, hz, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst x' y' z'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [← hf, ← hg]
  exact h

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
local instance laxDifferenceFunctorZero (A X : SSet.{u}) [Quasicategory X] [HasZeroVertex X] :
    HasZeroVertex ((ihom A).obj X) := functorHasZeroVertex A X

local instance laxDifferenceFunctorZeroMorphisms (A X : SSet.{u})
    [Quasicategory X] [HasZeroVertex X] :
    HasZeroMorphisms ((ihom A).obj X).HomotopyCategory :=
  hasZeroMorphisms_ho

end SerrePositivity.KST.LocalizingInvariants
