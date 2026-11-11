module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

/-!
概要：元の指定同型の二段の後合成と始域制限を、一つの後合成にまとめる。
方針：前後合成の交換と後合成の結合則を抽象的に合成する。
規約：元の指定値を保持。使われ方：大きな指定三角形の値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 二段の後合成と始域制限は、同じ合成射の後合成と始域制限に等しい。 -/
lemma functorIso_postcomp_precomp_postcomp {A X Y Z W : SSet.{u}}
    {f g : X ⟶ Y} (e : FunctorIso f g) (p : Y ⟶ Z) (a : A ⟶ X) (q : Z ⟶ W) :
    ((e.postcomp p).precomp a).postcomp q = (e.postcomp (p ≫ q)).precomp a := by
  rw [functorIso_precomp_postcomp, functorIso_postcomp_postcomp]

/-- 同じ結合則を、両端の関手の表示を同一化せずに指定値の型付き一致として保持する。 -/
lemma functorIso_postcomp_precomp_postcomp_heq {A X Y Z W : SSet.{u}}
    {f g : X ⟶ Y} (e : FunctorIso f g) (p : Y ⟶ Z) (a : A ⟶ X) (q : Z ⟶ W) :
    HEq (((e.postcomp p).precomp a).postcomp q) ((e.postcomp (p ≫ q)).precomp a) :=
  heq_of_eq (functorIso_postcomp_precomp_postcomp e p a q)

end SerrePositivity.InfinityCategories.F2
