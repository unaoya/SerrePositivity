module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedWhiskerSquare
/-!
概要：指定同型の包含後の比較を、入力制限と同じ出力分解へ同時に移す。
方針：同じ前後合成の異種等式を、実可換正方形に沿って正規化する。
規約：元の指定値を保つ。使われ方：K-flat の双加群同型作用と半自由 raw 比較の照合。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 同じ指定同型の包含後の回収は、入力制限と後続分解を合わせても保たれる。 -/
lemma functorIso_lifted_restriction_resolution_heq {A B C D S Y : SSet.{u}}
    {f g : A ⟶ B} {f' g' : C ⟶ D}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (i : A ⟶ C) (j : B ⟶ D) (p : S ⟶ A) (p' : S ⟶ C) (q : D ⟶ Y)
    (hf : i ≫ f' = f ≫ j) (hg : i ≫ g' = g ≫ j)
    (he : HEq (e.postcomp j) (e'.precomp i)) (hs : p ≫ i = p') :
    HEq ((e.postcomp (j ≫ q)).precomp p) ((e'.precomp p').postcomp q) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq (e'.precomp i) (e.postcomp j) hf hg he p
  have hh := hp.trans ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e' i p)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq e' hs))
  have hF : p' ≫ f' = p ≫ (f ≫ j) := by rw [← hs, Category.assoc, hf]
  have hG : p' ≫ g' = p ≫ (g ≫ j) := by rw [← hs, Category.assoc, hg]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (e'.precomp p') ((e.postcomp j).precomp p)
    hF hG hh q
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
