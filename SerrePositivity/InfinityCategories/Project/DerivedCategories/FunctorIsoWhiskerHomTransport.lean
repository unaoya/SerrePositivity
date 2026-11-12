module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerHEq
/-!
概要：元の通常 tensor 比較の半自由制限と共通出力分解後の射を回収する。
方針：端点の等式・同じ同型の値・実前後合成を不透明な補題で接続する。
規約：比較の指定値・計算上限を変更しない。使われ方：κ の右変数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorIso_precomp_postcomp_hom_transport
    {A X Y Z : SSet.{w}} {f g : X ⟶ Y} {f' g' : A ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (I : X ⟶ A) (L : Y ⟶ Z)
    (hf : f = I ≫ f') (hg : g = I ≫ g') (he : HEq e (e'.precomp I)) :
    HEq (e.postcomp L).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (I ≫ f') (I ≫ g') L
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' I e'.hom)) := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq e (e'.precomp I) hf hg he
  have hh' : HEq e.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' I e'.hom) :=
    hh.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed e' I))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_heq e _ hf hg hh' L
end SerrePositivity.InfinityCategories.Project.DerivedCategories
