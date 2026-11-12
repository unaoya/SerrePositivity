module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeDomainHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomWhiskering

/-!
概要：全余錐から定値図式への射を、余錐単位と頂点側の制限で因子化する。
方針：底包含から右頂点への標準ホモトピーの自然性を使う。
規約：元の全余錐と指定した射を保持する。
使われ方：余極限関手の全パラメータ Hom 対応。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SSet.Truncated.HomotopyCategory

/-- 概要：底制限は元の余錐の単位と右頂点への定値制限で因子化する。
方針：標準形状ホモトピーの自然性で、定値標的の成分を恒等射へ簡約する。
規約：全余錐から定値図式への元の射を使う。
使われ方：普遍余錐の Hom 対応と単位の照合。 -/
lemma precompositionHomotopy_constant_naturality {A B X : SSet.{u}}
    {f g : A ⟶ B} (T : SSet.Homotopy f g) (H : B ⟶ X) (y : X _⦋0⦌)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y)) :
    (hoFunctor.map ((pre f).app X)).toFunctor.map α =
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp T H)) ≫
      (hoFunctor.map ((pre g).app X)).toFunctor.map α := by
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans T X).naturality α
  erw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app] at hn
  have hc := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp T (SSet.const y))
    (by simp only [SSet.comp_const]) (by simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp, SSet.comp_const])
  rw [hc] at hn
  simp only [SSet.comp_const] at hn
  exact (Category.comp_id _).symm.trans hn

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
