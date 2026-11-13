module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
概要：係数環と加群の宇宙を分離した、加群の filtered 余極限の完全性。
方針：加法群への忘却関手が有限極限を保ち反映し、余極限を保つことを使う。
規約：整数環を持ち上げたり係数加群を縮小したりしない。
使われ方：Frobenius 順極限後の共通アフィン細分の H の比較。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v

/-- 任意の大きさの係数環上の加群で、同じ宇宙の filtered 余極限は完全。 -/
theorem moduleCatFiltered_hasExactColimitsOfShape
    (R : Type v) [Ring R] (J : Type u) [SmallCategory J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{u} R) :=
  HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

end SerrePositivity.AlgebraicGeometry
