module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! 単体集合同型による座標変更は、Kan 仮定を加えず同じ実ホモトピー逆を移す。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet

lemma dgGluingHomotopyEquivalence_precomp_iso_iff {A B T : SSet.{u}}
    (e : A ≅ B) (f : B ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (e.hom ≫ f) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  constructor
  · rintro ⟨g, ⟨H⟩, ⟨K⟩⟩
    refine ⟨g ≫ e.hom, ?_, ?_⟩
    · refine ⟨?_⟩
      have H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H e.inv) e.hom
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id,
        Category.id_comp, Iso.inv_hom_id] using H'
    · refine ⟨?_⟩
      simpa only [Category.assoc] using K
  · rintro ⟨g, ⟨H⟩, ⟨K⟩⟩
    refine ⟨g ≫ e.inv, ?_, ?_⟩
    · refine ⟨?_⟩
      have H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H e.hom) e.inv
      simpa only [Category.assoc, Category.comp_id, Category.id_comp, Iso.hom_inv_id] using H'
    · refine ⟨?_⟩
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using K

lemma dgGluingHomotopyEquivalence_postcomp_iso_iff {A B T : SSet.{u}}
    (f : A ⟶ B) (e : B ≅ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ≫ e.hom) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  constructor
  · rintro ⟨g, ⟨H⟩, ⟨K⟩⟩
    refine ⟨e.hom ≫ g, ?_, ?_⟩
    · refine ⟨?_⟩
      simpa only [Category.assoc] using H
    · refine ⟨?_⟩
      have K' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp K e.hom) e.inv
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Category.id_comp] using K'
  · rintro ⟨g, ⟨H⟩, ⟨K⟩⟩
    refine ⟨e.inv ≫ g, ?_, ?_⟩
    · refine ⟨?_⟩
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using H
    · refine ⟨?_⟩
      have K' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp K e.inv) e.hom
      simpa only [Category.assoc, Category.comp_id, Category.id_comp, Iso.inv_hom_id] using K'

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
