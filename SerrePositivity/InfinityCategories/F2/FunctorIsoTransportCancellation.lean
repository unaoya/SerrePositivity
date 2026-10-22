module

public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransport

/-!
概要：明示した実両端へ戻した同じ指定比較を、逆との合成で厳密に消去する。
方針：両端の等式だけを消去し、元の三比較の合成関係を使う。
規約：指定された同型の値を保持。使われ方：元の三角形の下側輸送比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実両端へ移した指定前置比較は、その逆との合成で消去できる。 -/
lemma functorIsoOfEq_symm_cancel_prefix {A X : SSet.{u}} {f g h f' g' : A ⟶ X}
    (e : FunctorIso f g) (d : FunctorIso f h) (r : FunctorIso g h)
    (hf : f = f') (hg : g = g') (hd : e ≪≫ r = d) :
    (functorIsoOfEq e hf hg).symm ≪≫ functorIsoOfEq d hf rfl =
      functorIsoOfEq r hg rfl := by
  cases hf
  cases hg
  dsimp only [functorIsoOfEq]
  rw [← hd, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.F2
