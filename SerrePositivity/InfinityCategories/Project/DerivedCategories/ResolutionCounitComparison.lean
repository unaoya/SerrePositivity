module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：二つの指定余単位の比較は、入力写像の合成に対して cocycle 則を満たす。
方針：同じ前後合成の交換則で中央の指定余単位とその逆を消す。
規約：余単位を選び直さない。使われ方：指定出力分解の前合成の合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 二つの指定余単位を、同じ入力写像に沿って比較する全関手同型。 -/
def resolutionCounitComparison {A B : SSet.{u}} {f : A ⟶ A} {g : B ⟶ B}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (𝟙 A)) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (𝟙 B)) (h : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ h) (h ≫ g) := e.postcomp h ≪≫ (d.precomp h).symm
/-- 指定余単位の比較の二段合成は、同じ合成入力写像の比較に厳密に一致する。 -/
lemma resolutionCounitComparison_comp {A B C : SSet.{u}}
    {f : A ⟶ A} {g : B ⟶ B} {t : C ⟶ C}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (𝟙 A)) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (𝟙 B)) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t (𝟙 C))
    (h : A ⟶ B) (k : B ⟶ C) :
    resolutionCounitComparison e a (h ≫ k) =
      (resolutionCounitComparison e d h).postcomp k ≪≫
        (resolutionCounitComparison d a k).precomp h := by
  simp only [resolutionCounitComparison, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
