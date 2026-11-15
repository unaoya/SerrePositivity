module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Basic

/-!
概要：有限な添字に、元の等号判定を保った順序を与える。
方針：既存の Fin との同型で順序を引き戻し、等号判定の投影を元のものに保つ。
規約：既存の複体と係数図式の DecidableEq を変更しない。
使われ方：同じタプル被覆に順序つきの増大写像の API を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/-- 有限な添字の、元の等号判定と定義上整合する順序。 -/
@[instance_reducible]
def cechFiniteIndexOrder (α : Type) [Fintype α] [d : DecidableEq α] : LinearOrder α :=
  let o := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  { o with
    toDecidableEq := d
    compare_eq_compareOfLessAndEq := by
      intro a b
      exact (o.compare_eq_compareOfLessAndEq a b).trans
        (congrArg (fun e : DecidableEq α ↦
          @compareOfLessAndEq α a b o.toLT (o.toDecidableLT a b) e)
          (Subsingleton.elim _ d)) }

/-- 移送した順序の等号判定は、元の係数図式のものと定義上同じ。 -/
theorem cechFiniteIndexOrder_decidableEq (α : Type) [Fintype α] [d : DecidableEq α] :
    (cechFiniteIndexOrder α).toDecidableEq = d := rfl

end SerrePositivity.AlgebraicGeometry
