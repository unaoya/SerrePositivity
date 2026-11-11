module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionComparisonComposition
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
/-- 同じ指定比較の三重合成の左経路を、共通の水平比較と対応する経路へ展開する。 -/
lemma comparisonComposition_left_path {X₀ X₁ X₂ X₃ A₀ A₁ A₂ A₃ : SSet.{u}}
    [Quasicategory X₂] [Quasicategory A₃]
    (L₀ : X₀ ⟶ A₀) (L₁ : X₁ ⟶ A₁) (L₂ : X₂ ⟶ A₂) (L₃ : X₃ ⟶ A₃)
    (F₀ : A₀ ⟶ A₁) (F₁ : A₁ ⟶ A₂) (F₂ : A₂ ⟶ A₃)
    (G₀ : X₀ ⟶ X₁) (G₁ : X₁ ⟶ X₂) (G₂ : X₂ ⟶ X₃)
    (F₀₂ : A₀ ⟶ A₂) (T : A₀ ⟶ A₃) (G₀₂ : X₀ ⟶ X₂) (H : X₀ ⟶ X₃)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F₀) (G₀ ≫ L₁))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₁ ≫ F₁) (G₁ ≫ L₂))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₂ ≫ F₂) (G₂ ≫ L₃))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F₀₂) (G₀₂ ≫ L₂)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ T) (H ≫ L₃))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F₀ ≫ F₁) F₀₂) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F₀₂ ≫ F₂) T)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G₀ ≫ G₁) G₀₂) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G₀₂ ≫ G₂) H)
    (hk : k.precomp L₀ ≪≫ d = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₂ F₀ G₀ F₁ G₁ a b ≪≫
      α.postcomp L₂)
    (hl : l.precomp L₀ ≪≫ t = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₂ L₃ F₀₂ G₀₂ F₂ G₂ d c ≪≫
      β.postcomp L₃) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (k.postcomp F₂ ≪≫ l) L₀ ≪≫ t =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₂ L₃ (F₀ ≫ F₁) (G₀ ≫ G₁) F₂ G₂
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₂ F₀ G₀ F₁ G₁ a b) c ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (α.postcomp G₂ ≪≫ β) L₃ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans]
  let ab := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₂ F₀ G₀ F₁ G₁ a b
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange α c
  calc
    _ = (k.postcomp F₂).precomp L₀ ≪≫ (l.precomp L₀ ≪≫ t) := Iso.trans_assoc _ _ _
    _ = (k.postcomp F₂).precomp L₀ ≪≫
        (d.postcomp F₂ ≪≫ c.precomp G₀₂ ≪≫ β.postcomp L₃) := by
      rw [hl]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, Iso.trans_assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (k.precomp L₀ ≪≫ d) F₂ ≪≫
        c.precomp G₀₂ ≪≫ β.postcomp L₃ := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp, Iso.trans_assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (ab ≪≫ α.postcomp L₂) F₂ ≪≫
        c.precomp G₀₂ ≪≫ β.postcomp L₃ := by rw [hk]
    _ = ab.postcomp F₂ ≪≫ ((α.postcomp L₂).postcomp F₂ ≪≫ c.precomp G₀₂) ≪≫
        β.postcomp L₃ := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, Iso.trans_assoc]
    _ = ab.postcomp F₂ ≪≫ (c.precomp (G₀ ≫ G₁) ≪≫ α.postcomp (G₂ ≫ L₃)) ≪≫
        β.postcomp L₃ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp, hx]
    _ = _ := by
      simp only [ab, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp, Iso.trans_assoc]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
