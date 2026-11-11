module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq

/-!
概要：指定逆同型の型付き一致から、元の指定同型の一致を戻す。
方針：実両端の等式を保って逆を取り、二度の逆を抽象的な射で消去する。
規約：指定値を選び直さない。使われ方：元の大きい右 Hom 比較の表示変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実両端での逆同型の一致は、元の指定同型と指定逆の一致を与える。 -/
lemma functorIso_heq_symm_of_symm_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (d : FunctorIso f g) (e : FunctorIso f' g') (hf : f = g') (hg : g = f')
    (h : HEq e.symm d) : HEq e d.symm := by
  have hh := functorIso_symm_heq_of_heq d e.symm hf hg h
  simpa only [Iso.symm_symm_eq] using hh

end SerrePositivity.InfinityCategories.F2
