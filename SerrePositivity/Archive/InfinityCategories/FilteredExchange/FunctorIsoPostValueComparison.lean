module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

/-!
概要：同じ合成値射への像の指定比較を、二段の後合成による同じ指定値へ移す。
方針：後合成の結合則と型付き一致の推移を抽象的に合成する。
規約：指定された両比較を保持。使われ方：raw fiber 比較の固定値への射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 合成値射への元の指定値の一致は、同じ二段の後合成の指定値にもそのまま移る。 -/
lemma functorIso_postcomp_pair_comparison_heq {A B C D : SSet.{u}}
    {f g : A ⟶ B} (e : FunctorIso f g) (p : B ⟶ C) (v : C ⟶ D)
    {f' g' : A ⟶ D} (d : FunctorIso f' g')
    (h : HEq (e.postcomp (p ≫ v)) d) : HEq ((e.postcomp p).postcomp v) d :=
  (heq_of_eq (functorIso_postcomp_postcomp e p v)).trans h

end SerrePositivity.InfinityCategories.F2
