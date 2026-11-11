module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

/-!
概要：逆比較の実端点補正と二段の後合成を、元の前合成との交換へ移す。
方針：実端点等式を消去してから、変数のまま逆と前後合成の交換を証明する。
規約：具体的な大きい端点を展開しない。使われ方：逆第一辺因子の最後辺輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 逆前合成比較の実端点補正後の二段の像は、元の後合成・前合成交換後の同じ逆。 -/
lemma functorIsoOfEq_inverse_pre_post_value_heq {A X Y Z W : SSet.{u}}
    {f g : X ⟶ Y} (e : FunctorIso f g) (p : A ⟶ X)
    {h : A ⟶ Y} (hh : p ≫ f = h) (r : Y ⟶ Z) (s : Z ⟶ W) :
    HEq (((functorIsoOfEq (e.precomp p).symm rfl hh).postcomp r).postcomp s)
      (((e.postcomp r).precomp p).postcomp s).symm := by
  subst h
  change HEq ((FunctorIso.postcomp (e.precomp p).symm r).postcomp s) _
  rw [functorIso_postcomp_symm, functorIso_postcomp_symm, functorIso_precomp_postcomp]

/-- 二段の後合成は、二つの元の指定比較の合成を厳密に保つ。 -/
lemma functorIso_postcomp_trans_twice {A X Y Z : SSet.{u}} {f g h : A ⟶ X}
    (e : FunctorIso f g) (d : FunctorIso g h) (p : X ⟶ Y) (q : Y ⟶ Z) :
    ((FunctorIso.postcomp (e ≪≫ d) p).postcomp q) =
      (e.postcomp p).postcomp q ≪≫ (d.postcomp p).postcomp q := by
  rw [functorIso_postcomp_trans, functorIso_postcomp_trans]

end SerrePositivity.InfinityCategories.F2
