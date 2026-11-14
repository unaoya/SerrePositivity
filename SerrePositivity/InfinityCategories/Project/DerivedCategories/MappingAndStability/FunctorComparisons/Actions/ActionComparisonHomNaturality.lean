module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionComparisonComposition
/-!
概要：元の ξ の水平二重比較の任意全関手射に対する自然性を証明する。
方針：二つの指定自然性四角形と全前後合成の交換則を使う。
規約：射の可逆性は不要。使われ方：元の κ の全射自然性の移送。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "po" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
local notation "pr" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
lemma comparisonCompositionIso_hom_naturality {X Y Z A B C : SSet.{u}}
    [Quasicategory Y] [Quasicategory B] [Quasicategory C]
    (L₀ : X ⟶ A) (L₁ : Y ⟶ B) (L₂ : Z ⟶ C)
    (F F' : A ⟶ B) (H H' : B ⟶ C) (G G' : X ⟶ Y) (K K' : Y ⟶ Z)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F) (G ≫ L₁)) (a' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₀ ≫ F') (G' ≫ L₁))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₁ ≫ H) (K ≫ L₂)) (b' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L₁ ≫ H') (K' ≫ L₂))
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F F') (e₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G G')
    (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H H') (d₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom K K')
    (ha : a.hom ≫ po G G' L₁ e₀ = pr F F' L₀ e ≫ a'.hom)
    (hb : b.hom ≫ po K K' L₂ d₀ = pr H H' L₁ d ≫ b'.hom) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₂ F G H K a b).hom ≫
        po (G ≫ K) (G' ≫ K') L₂ (po G G' K e₀ ≫ pr K K' G' d₀) =
      pr (F ≫ H) (F' ≫ H') L₀ (po F F' H e ≫ pr H H' F' d) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₂ F' G' H' K' a' b').hom := by
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange_typed e₀ b.hom
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange_typed a'.hom d
  calc
    _ = po (L₀ ≫ F) (G ≫ L₁) H a.hom ≫
        (pr (L₁ ≫ H) (K ≫ L₂) G b.hom ≫
          po (G ≫ K) (G' ≫ K) L₂ (po G G' K e₀)) ≫
        po (G' ≫ K) (G' ≫ K') L₂ (pr K K' G' d₀) := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp, Category.assoc]
    _ = po (L₀ ≫ F) (G ≫ L₁) H a.hom ≫
        (po G G' (L₁ ≫ H) e₀ ≫ pr (L₁ ≫ H) (K ≫ L₂) G' b.hom) ≫
        po (G' ≫ K) (G' ≫ K') L₂ (pr K K' G' d₀) := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_postcomp] using
        congrArg (fun z => po (L₀ ≫ F) (G ≫ L₁) H a.hom ≫ z ≫
          po (G' ≫ K) (G' ≫ K') L₂ (pr K K' G' d₀)) h₀.symm
    _ = po (L₀ ≫ F) (G' ≫ L₁) H (a.hom ≫ po G G' L₁ e₀) ≫
        pr (L₁ ≫ H) (K' ≫ L₂) G' (b.hom ≫ po K K' L₂ d₀) := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_postcomp, Category.assoc]
    _ = po (L₀ ≫ F) (G' ≫ L₁) H (pr F F' L₀ e ≫ a'.hom) ≫
        pr (L₁ ≫ H) (K' ≫ L₂) G' (pr H H' L₁ d ≫ b'.hom) := by rw [ha, hb]
    _ = pr (F ≫ H) (F' ≫ H) L₀ (po F F' H e) ≫
        (po (L₀ ≫ F') (G' ≫ L₁) H a'.hom ≫ pr H H' (G' ≫ L₁) d) ≫
        pr (L₁ ≫ H') (K' ≫ L₂) G' b'.hom := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_precomp, Category.assoc]
    _ = pr (F ≫ H) (F' ≫ H) L₀ (po F F' H e) ≫
        (pr H H' (L₀ ≫ F') d ≫ po (L₀ ≫ F') (G' ≫ L₁) H' a'.hom) ≫
        pr (L₁ ≫ H') (K' ≫ L₂) G' b'.hom := by rw [h₁]
    _ = _ := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_precomp, Category.assoc]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
