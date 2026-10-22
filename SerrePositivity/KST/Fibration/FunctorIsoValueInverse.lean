module
public import SerrePositivity.KST.Fibration.FunctorIsoValue

/-! # 同じ指定関手同型の頂点評価は、その逆成分を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 任意の底で、同じ指定した逆二胞体の評価を回収する。 -/
theorem functorIsoValue_inv {K Y : SSet.{u}} {F G : K ⟶ Y}
    (e : FunctorIso F G) (x : K _⦋0⦌) :
    (functorIsoValue e x).inv = functorHomEvaluate e.inv x := by
  apply (cancel_epi (functorIsoValue e x).hom).mp
  rw [Iso.hom_inv_id, functorIsoValue_hom, ← functorHomEvaluate_comp,
    e.hom_inv_id, functorHomEvaluate_id]

end SerrePositivity.KST.Fibration
