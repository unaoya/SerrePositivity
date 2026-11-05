module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValue

/-! # 同じ指定関手同型の頂点評価は、その逆成分を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 任意の底で、同じ指定した逆二胞体の評価を回収する。 -/
theorem functorIsoValue_inv {K Y : SSet.{u}} {F G : K ⟶ Y}
    (e : FunctorIso F G) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue e x).inv = functorHomEvaluate e.inv x := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue e x).hom).mp
  rw [Iso.hom_inv_id, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_hom, ← functorHomEvaluate_comp,
    e.hom_inv_id, functorHomEvaluate_id]

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIsoValue_inv := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_inv
