module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoWhiskerCancellation
/-!
概要：指定同型の包含後の異種等式を、同じ前後合成の可換正方形へ移す。
方針：元の指定値と端点等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：kernel の単位・結合 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 同じ指定同型の包含後の比較は、出力の可換正方形に沿う後合成を保つ。 -/
lemma functorIso_lifted_postcomp_square {A B X Y Z W : SSet.{u}}
    {f g : A ⟶ X} {f' g' : B ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (i : A ⟶ B) (j : X ⟶ Y) (q : X ⟶ Z) (k : Z ⟶ W) (q' : Y ⟶ W)
    (hf : i ≫ f' = f ≫ j) (hg : i ≫ g' = g ≫ j)
    (he : HEq (e.postcomp j) (e'.precomp i)) (hs : q ≫ k = j ≫ q') :
    HEq ((e.postcomp q).postcomp k) ((e'.postcomp q').precomp i) := by
  have h₁ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp e q k)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq e hs.symm
  have h₃ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp e j q').symm
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (e'.precomp i) (e.postcomp j) hf hg he q'
  have h₅ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp e' i q')
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
/-- 同じ指定同型の包含後の比較は、入力の可換正方形に沿う前合成を保つ。 -/
lemma functorIso_lifted_precomp_square {A B X Y Z W : SSet.{u}}
    {f g : X ⟶ Y} {f' g' : Z ⟶ W}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (i : X ⟶ Z) (j : Y ⟶ W) (p : A ⟶ X) (p' : B ⟶ Z) (k : A ⟶ B)
    (hf : i ≫ f' = f ≫ j) (hg : i ≫ g' = g ≫ j)
    (he : HEq (e.postcomp j) (e'.precomp i)) (hs : p ≫ i = k ≫ p') :
    HEq ((e.precomp p).postcomp j) ((e'.precomp p').precomp k) := by
  have h₁ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp e p j)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq (e'.precomp i) (e.postcomp j) hf hg he p
  have h₃ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e' i p)
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq e' hs
  have h₅ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e' p' k).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
