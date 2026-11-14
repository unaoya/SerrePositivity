module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionComparisonComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
/-!
概要：指定合成子の三重合成経路を、同じ比較の水平合成へ同定する。
方針：元の二つの合成子正方形と全関手同型の実交換則を使う。
規約：指定値と全関手同型を保つ。使われ方：元の導来 kernel 五角経路の移送。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 同じ指定比較の三重合成の右経路を、共通の水平比較と対応する経路へ展開する。 -/
lemma comparisonComposition_right_path {X₀ X₁ X₂ X₃ A₀ A₁ A₂ A₃ : SSet.{u}}
    [Quasicategory A₁] [Quasicategory A₃]
    (L₀ : X₀ ⟶ A₀) (L₁ : X₁ ⟶ A₁) (L₂ : X₂ ⟶ A₂) (L₃ : X₃ ⟶ A₃)
    (F₀ : A₀ ⟶ A₁) (F₁ : A₁ ⟶ A₂) (F₂ : A₂ ⟶ A₃)
    (G₀ : X₀ ⟶ X₁) (G₁ : X₁ ⟶ X₂) (G₂ : X₂ ⟶ X₃)
    (F₁₃ : A₁ ⟶ A₃) (T : A₀ ⟶ A₃) (G₁₃ : X₁ ⟶ X₃) (H : X₀ ⟶ X₃)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F₀) (G₀ ≫ L₁))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₁ ≫ F₁) (G₁ ≫ L₂))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₂ ≫ F₂) (G₂ ≫ L₃))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₁ ≫ F₁₃) (G₁₃ ≫ L₃)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ T) (H ≫ L₃))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F₁ ≫ F₂) F₁₃) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F₀ ≫ F₁₃) T)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G₁ ≫ G₂) G₁₃) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G₀ ≫ G₁₃) H)
    (hk : k.precomp L₁ ≪≫ d = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₁ L₂ L₃ F₁ G₁ F₂ G₂ b c ≪≫
      α.postcomp L₃)
    (hl : l.precomp L₀ ≪≫ t = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₃ F₀ G₀ F₁₃ G₁₃ a d ≪≫
      β.postcomp L₃) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (k.precomp F₀ ≪≫ l) L₀ ≪≫ t =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₃ F₀ G₀ (F₁ ≫ F₂) (G₁ ≫ G₂) a
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₁ L₂ L₃ F₁ G₁ F₂ G₂ b c) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (α.precomp G₀ ≪≫ β) L₃ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans]
  let bc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₁ L₂ L₃ F₁ G₁ F₂ G₂ b c
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange a k
  calc
    _ = (k.precomp F₀).precomp L₀ ≪≫ (l.precomp L₀ ≪≫ t) := Iso.trans_assoc _ _ _
    _ = (k.precomp F₀).precomp L₀ ≪≫
        (a.postcomp F₁₃ ≪≫ d.precomp G₀ ≪≫ β.postcomp L₃) := by
      rw [hl]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, Iso.trans_assoc]
    _ = ((k.precomp (L₀ ≫ F₀)).trans (a.postcomp F₁₃)) ≪≫
        d.precomp G₀ ≪≫ β.postcomp L₃ := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp, Iso.trans_assoc]
    _ = (a.postcomp (F₁ ≫ F₂) ≪≫ k.precomp (G₀ ≫ L₁)) ≪≫
        d.precomp G₀ ≪≫ β.postcomp L₃ := by rw [← hx]
    _ = a.postcomp (F₁ ≫ F₂) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (k.precomp L₁ ≪≫ d) G₀ ≪≫
        β.postcomp L₃ := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp, Iso.trans_assoc]
    _ = a.postcomp (F₁ ≫ F₂) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (bc ≪≫ α.postcomp L₃) G₀ ≪≫
        β.postcomp L₃ := by rw [hk]
    _ = _ := by
      simp only [bc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans,
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp, Iso.trans_assoc]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
