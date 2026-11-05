module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValueInverse

/-! # 同じ指定関手同型の頂点値は合成を保持する -/

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

/-- 始域の充填性を要求せず、元の指定合成の同じ頂点値を回収する。 -/
theorem functorIsoValue_trans {K Y : SSet.{u}} {F G H : K ⟶ Y}
    (e : FunctorIso F G) (f : FunctorIso G H) (x : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue (e ≪≫ f) x = _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue e x ≪≫ _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue f x := by
  apply Iso.ext
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_hom, functorHomEvaluate_comp]

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIsoValue_trans := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_trans
