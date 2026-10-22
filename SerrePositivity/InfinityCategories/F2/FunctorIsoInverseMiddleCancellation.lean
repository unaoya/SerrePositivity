module

public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransportCancellation

/-!
概要：実両端を合わせた三比較の合成則から、残余の逆と中間比較の合成を消去する。
方針：前置因子の消去式の逆を取り、同じ指定同型の合成順を戻す。
規約：三つの指定比較と両端の等式を保持。使われ方：元の長辺輸送の残余の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 実両端を揃えた元の残余の逆は、同じ中間比較との合成で次の残余の逆に消去される。 -/
lemma functorIsoOfEq_inverse_middle_cancel {A X : SSet.{u}} {f g h f' g' : A ⟶ X}
    (e : FunctorIso f g) (d : FunctorIso f h) (r : FunctorIso g h)
    (hf : f = f') (hg : g = g') (hd : e ≪≫ r = d) :
    (functorIsoOfEq d hf rfl).symm ≪≫ functorIsoOfEq e hf hg =
      (functorIsoOfEq r hg rfl).symm := by
  have hc := congrArg Iso.symm (functorIsoOfEq_symm_cancel_prefix e d r hf hg hd)
  simpa only [Iso.trans_symm, Iso.symm_symm_eq] using hc

end SerrePositivity.InfinityCategories.F2
