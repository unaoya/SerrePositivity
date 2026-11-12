module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichMiddleChange
/-!
概要：実 span の前後合成を三つの指定比較の差へ同定する。
方針：同じ同型の前後合成と共通始点の相殺を使う。
規約：追加の選択は不要。使われ方：diagonal の実模型比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIso_whisker_span_value {X A B Y : SSet.{u}}
    (s : X ⟶ A) (t : B ⟶ Y) (F0 F1 Fmid : A ⟶ B) (H : X ⟶ Y)
    (b0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso Fmid F0) (b1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso Fmid F1)
    (a0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso H (s ≫ F0 ≫ t)) (a1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso H (s ≫ F1 ≫ t))
    (a2 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso H (s ≫ Fmid ≫ t))
    (h0 : (b0.postcomp t).precomp s = a2.symm ≪≫ a0)
    (h1 : (b1.postcomp t).precomp s = a2.symm ≪≫ a1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (b0.symm ≪≫ b1) t).precomp s = a0.symm ≪≫ a1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm, h0, h1,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
