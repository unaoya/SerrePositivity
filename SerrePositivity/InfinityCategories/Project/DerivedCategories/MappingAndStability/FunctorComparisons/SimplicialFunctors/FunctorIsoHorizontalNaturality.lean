module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionComparisonHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPostcompIdentity
/-!
概要：二つの全関手比較の水平合成は任意全関手射に自然である。
方針：指定比較四角形の水平合成則を恒等の辺へ適用する。
規約：射の可逆性を要求しない。使われ方：一般 cell 合成比較の自然性。
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
lemma functorIsoHorizontal_hom_naturality {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z]
    {F F' G G' : X ⟶ Y} {H H' K K' : Y ⟶ Z}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (a' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F' G')
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso H K) (b' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso H' K')
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F F') (e' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G G')
    (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H H') (d' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom K K')
    (ha : a.hom ≫ e' = e ≫ a'.hom) (hb : b.hom ≫ d' = d ≫ b'.hom) :
    (a.postcomp H ≪≫ b.precomp G).hom ≫
        (po G G' K e' ≫ pr K K' G' d') =
      (po F F' H e ≫ pr H H' F' d) ≫ (a'.postcomp H' ≪≫ b'.precomp G').hom := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso_hom_naturality (𝟙 X) (𝟙 Y) (𝟙 Z)
    F F' H H' G G' K K' a a' b b' e e' d d'
    (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_id] using! ha)
    (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_id] using! hb)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_id] using! h
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
