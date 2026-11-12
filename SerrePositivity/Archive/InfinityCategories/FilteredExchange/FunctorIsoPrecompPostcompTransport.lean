module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の同型の実両端の表示変更を、前合成と後合成を通して保持する。
方針：両端の射の等式だけを消去する。
規約：元の指定値を保持。使われ方：下側因子を元の実長辺上の輸送比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実両端への表示変更は、指定した前合成と後合成の後でも同じ指定値を保つ。 -/
lemma functorIsoOfEq_precomp_postcomp_heq {A X Y Z : SSet.{u}}
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : A ⟶ X) (q : Y ⟶ Z) :
    HEq (((functorIsoOfEq e hf hg).precomp p).postcomp q)
      ((e.precomp p).postcomp q) := by
  cases hf
  cases hg
  rfl

end SerrePositivity.InfinityCategories.F2
