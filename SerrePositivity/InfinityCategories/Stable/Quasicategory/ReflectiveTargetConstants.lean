module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantAdjunct
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorMap
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingParameters

/-!
分割で生成：docstring を書き直すこと
概要：反射の左関手による定値関手間の Hom の比較は、局所な終点で全単射。
方針：任意の関手圏の比較を使い、定値関手の合成の厳密比較で両端を正規化する。
規約：元の後合成を表す写像。使われ方：実写像空間の q による比較の同値性。
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

/-- 関手による後合成を、元の像の頂点での定値関手へ正規化する。 -/
def constantFunctorPostMap {X Y : SSet.{u}} (F : X ⟶ Y) (A : SSet.{u})
    (x y : X _⦋0⦌) (α : ConstantFunctorHom A X x y) :
    ConstantFunctorHom A Y (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  (constantFunctorCompIso A x F).inv ≫
    (hoFunctor.map ((ihom A).map F)).toFunctor.map α ≫ (constantFunctorCompIso A y F).hom

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (hG : IsFullyFaithful G)

lemma intervalFunctorMap_familyHom_post {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) (F : X ⟶ Y) :
    intervalFamilyHom (f ≫ intervalFunctorMap F x y) =
      constantFunctorPostMap F A x y (intervalFamilyHom f) :=
  intervalFunctorMap_familyHom f F

end SerrePositivity.KST.LocalizingInvariants
