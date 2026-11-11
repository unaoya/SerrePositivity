module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の前後合成の交換を、実両端の結合表示の等式で固定したまま使う。
方針：同じ指定比較の表示変更と元の前後合成の交換を合成する。
規約：元の値を保持。使われ方：長辺二因子の大きな実輸送の型展開を分割する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 前後合成を交換した同じ指定値の、始点と終点の結合表示を明示的に保つ。 -/
lemma functorIso_post_pre_source_eq_pre_post_target {A X Y Z : SSet.{u}}
    {f g : X ⟶ Y} (e : FunctorIso f g) (q : A ⟶ X) (v : Y ⟶ Z) :
    functorIsoOfEq ((e.postcomp v).precomp q) (Category.assoc q f v).symm rfl =
      functorIsoOfEq ((e.precomp q).postcomp v) rfl (Category.assoc q g v) := by
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    ((heq_of_eq (functorIso_precomp_postcomp e q v).symm).trans
      (functorIsoOfEq_heq _ _ _).symm))

end SerrePositivity.InfinityCategories.F2
