module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite

/-!
概要：元のnerve反転同型の逆を、同じ射列の逆反転へ評価する。
方針：元の逆反転の往復等式を、同じ同型の逆で送る。
規約：IS-W2 R03dの既存の係数移送則。逆を選び直さない。
使われ方：twisted arrowの左射影を、元の反変の始域関手と厳密に合わせる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open CategoryTheory SSet
open scoped Simplicial
variable {C : Type u} [SmallCategory C]

/-- 同じnerve反転同型の逆の評価は、元の同じ逆反転の射列。 -/
theorem nerveOppositeIso_inv_apply {n : ℕ} (σ : ComposableArrows Cᵒᵖ n) :
    (nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌) σ =
      SSet.opObjEquiv.symm (nerveUnreverseChain σ) := by
  have hr := nerveReverse_unreverse σ
  change (nerveOppositeIso (C := C)).hom.app (Opposite.op ⦋n⦌)
    (SSet.opObjEquiv.symm (nerveUnreverseChain σ)) = σ at hr
  have he := congrArg (fun x => (nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌) x) hr
  change ((nerveOppositeIso (C := C)).hom ≫ (nerveOppositeIso (C := C)).inv).app
    (Opposite.op ⦋n⦌) (SSet.opObjEquiv.symm (nerveUnreverseChain σ)) = _ at he
  rw [Iso.hom_inv_id] at he
  exact he.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
