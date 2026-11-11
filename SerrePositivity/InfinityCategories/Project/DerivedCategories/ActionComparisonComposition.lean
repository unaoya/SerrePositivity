module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：指定比較の水平合成とその結合律を、同じ全関手同型として構成する。
方針：元の前後合成の恒等式と同型の通常合成則を使う。
規約：別の比較を選ばない。使われ方：元の導来 kernel 五角経路の共通前置比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 指定比較の二つの正方形を、同じ全関手同型の前後合成で水平に合成する。 -/
def comparisonCompositionIso {X₀ X₁ X₂ A₀ A₁ A₂ : SSet.{u}}
    (L₀ : X₀ ⟶ A₀) (L₁ : X₁ ⟶ A₁) (L₂ : X₂ ⟶ A₂)
    (F : A₀ ⟶ A₁) (G : X₀ ⟶ X₁) (H : A₁ ⟶ A₂) (K : X₁ ⟶ X₂)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F) (G ≫ L₁)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₁ ≫ H) (K ≫ L₂)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F ≫ H) (G ≫ K ≫ L₂) := a.postcomp H ≪≫ b.precomp G
/-- 同じ指定比較の水平三重合成は、全関手同型として結合的。 -/
lemma comparisonCompositionIso_assoc {X₀ X₁ X₂ X₃ A₀ A₁ A₂ A₃ : SSet.{u}}
    (L₀ : X₀ ⟶ A₀) (L₁ : X₁ ⟶ A₁) (L₂ : X₂ ⟶ A₂) (L₃ : X₃ ⟶ A₃)
    (F₀ : A₀ ⟶ A₁) (F₁ : A₁ ⟶ A₂) (F₂ : A₂ ⟶ A₃)
    (G₀ : X₀ ⟶ X₁) (G₁ : X₁ ⟶ X₂) (G₂ : X₂ ⟶ X₃)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F₀) (G₀ ≫ L₁))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₁ ≫ F₁) (G₁ ≫ L₂))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₂ ≫ F₂) (G₂ ≫ L₃)) :
    comparisonCompositionIso L₀ L₂ L₃ (F₀ ≫ F₁) (G₀ ≫ G₁) F₂ G₂
      (comparisonCompositionIso L₀ L₁ L₂ F₀ G₀ F₁ G₁ a b) c =
    comparisonCompositionIso L₀ L₁ L₃ F₀ G₀ (F₁ ≫ F₂) (G₁ ≫ G₂) a
      (comparisonCompositionIso L₁ L₂ L₃ F₁ G₁ F₂ G₂ b c) := by
  simp only [comparisonCompositionIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp, Iso.trans_assoc]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
