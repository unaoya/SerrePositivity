module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteCoproductsOnBase
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：元の小さい底の有限余積保存は全関手同型で不変。
方針：同じ全余錐上へ比較同型を制限する。
規約：元の指定全図式と余錐を保つ。
使われ方：元の左 Kan 延長の可逆単位で有限条件を回収する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：同型な元の全関手は小さい底の同じ有限余積を保存する。
方針：元の全余錐の像の関手同型で余極限性を移す。
規約：元の底の有限余積を変更しない。
使われ方：指定左 Kan 単位による有限条件の比較。 -/
lemma PreservesFiniteCoproductsOnBase.of_functorIso
    {C : SSet.{u}} {D : SSet.{u + 1}} [Quasicategory D]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D}
    (h : PreservesFiniteCoproductsOnBase F) (e : FunctorIso F G) :
    PreservesFiniteCoproductsOnBase G := by
  intro I hI p c hc
  exact (h I p c hc).of_functorIso (e.precomp (JoinCocone.ulift.{u, u + 1} c).val)

end SerrePositivity.InfinityCategories.F2.Presentable
