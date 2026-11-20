module


public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
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
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore

/-!
分割で生成：docstring を書き直すこと
概要：全頂点を覆う制限に沿って、元の商の関手 core 逆像を厳密に回収する。
方針：全高次単体の core 所属を各頂点評価に戻し、元の制限の全境界充填を制限する。
規約：商の局所化同値や Hom の充満忠実性はこの制限射の RLP から推論しない。
使われ方：c5 の実有限図式の貼合せを、指定部分族を保って元の相対図式内で行う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma comp_app_congr {T U V : SSet.{u}} {f : T ⟶ U} {g : U ⟶ V} {h : T ⟶ V}
    (e : f ≫ g = h) (n : SimplexCategoryᵒᵖ) (s : T.obj n) :
    g.app n (f.app n s) = h.app n s := congrArg (fun k : T ⟶ V => k.app n s) e

/-- 同じ商の後合成による、全図式の元の厳密 core 逆像。 -/
def relativeFunctorCore {B C : SSet.{u}} (q : B ⟶ C) (K : SSet.{u}) :
    ((ihom K).obj B).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).preimage ((ihom K).map q)

/-- 同じ core 逆像から商図式の core への元の射影。 -/
def relativeFunctorCoreQuotient {B C : SSet.{u}} (q : B ⟶ C) (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C) : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).fromPreimage ((ihom K).map q)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
