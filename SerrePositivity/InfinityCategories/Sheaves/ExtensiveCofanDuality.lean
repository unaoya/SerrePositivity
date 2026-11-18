module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Opposites

/-!
概要：同じ有限族の cofan と反対圏の fan を、脚を変えずに移す。
方針：既存の fan・cofan の普遍射を反転し、各脚と一意性を反対圏で戻す。
  文献対応：HTT 6.2.2.6 の extensive 位相での係数移送。
規約：通常圏の双対の法則。有限性は必要なく、空族も含む。
使われ方：S1 の元の有限積保存の指定錐へ戻す係数移送。
-/

@[expose] public noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {ι : Type w}

/-- 同じ cofan の脚を反転した指定 fan。 -/
def cofanToOppositeFan {B : ι → C} (c : Cofan B) : Fan (fun i => Opposite.op (B i)) :=
  Fan.mk (Opposite.op c.pt) (fun i => (c.inj i).op)

/-- 反対圏の同じ fan の脚を戻した指定 cofan。 -/
def fanToUnopCofan {B : ι → Cᵒᵖ} (c : Fan B) : Cofan (fun i => (B i).unop) :=
  Cofan.mk c.pt.unop (fun i => (c.proj i).unop)

/-- 余積の同じ普遍射を反転すると、指定 fan の積の普遍性になる。 -/
def cofanToOppositeFan_isLimit {B : ι → C} (c : Cofan B) (hc : IsColimit c) :
    IsLimit (cofanToOppositeFan c) := by
  refine Fan.IsLimit.mk _ (fun t => (hc.desc (fanToUnopCofan t)).op) ?_ ?_
  · intro t i
    apply Quiver.Hom.unop_inj
    exact hc.fac (fanToUnopCofan t) (Discrete.mk i)
  · intro t m hm
    apply Quiver.Hom.unop_inj
    apply hc.hom_ext
    intro i
    exact (congrArg Quiver.Hom.unop (hm i.as)).trans
      (hc.fac (fanToUnopCofan t) i).symm

/-- 積の同じ普遍射を戻すと、指定 cofan の余積の普遍性になる。 -/
def fanToUnopCofan_isColimit {B : ι → Cᵒᵖ} (c : Fan B) (hc : IsLimit c) :
    IsColimit (fanToUnopCofan c) := by
  refine Cofan.IsColimit.mk _
    (fun t => (hc.lift (Fan.mk (Opposite.op t.pt) (fun i => (t.inj i).op))).unop) ?_ ?_
  · intro t i
    apply Quiver.Hom.op_inj
    exact hc.fac (Fan.mk (Opposite.op t.pt) (fun j => (t.inj j).op)) (Discrete.mk i)
  · intro t m hm
    apply Quiver.Hom.op_inj
    apply hc.hom_ext
    intro i
    exact (congrArg Quiver.Hom.op (hm i.as)).trans
      (hc.fac (Fan.mk (Opposite.op t.pt) (fun j => (t.inj j).op)) i).symm

end SerrePositivity.InfinityCategories.Sheaves
