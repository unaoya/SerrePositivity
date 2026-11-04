module
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValueInverse

/-! # 同じ指定関手同型の頂点値は合成を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 始域の充填性を要求せず、元の指定合成の同じ頂点値を回収する。 -/
theorem functorIsoValue_trans {K Y : SSet.{u}} {F G H : K ⟶ Y}
    (e : FunctorIso F G) (f : FunctorIso G H) (x : K _⦋0⦌) :
    functorIsoValue (e ≪≫ f) x = functorIsoValue e x ≪≫ functorIsoValue f x := by
  apply Iso.ext
  simp only [Iso.trans_hom, functorIsoValue_hom, functorHomEvaluate_comp]

end SerrePositivity.KST.Fibration
