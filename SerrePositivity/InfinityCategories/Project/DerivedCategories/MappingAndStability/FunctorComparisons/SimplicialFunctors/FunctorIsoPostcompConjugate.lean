module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskerExchange
/-!
概要：指定した後続関手の比較により、同じ実ホモトピーの可逆な像を移す。
方針：元の後続比較による共役を構成し、非可逆変換の交換則で元の実辺の類を回収する。
規約：元のホモトピーの可逆性を仮定しない。使われ方：augmentation の raw factor 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 同じ後続比較によって、指定変換の可逆な像を次の後続関手へ移す。 -/
def functorIsoPostcompConjugate {X Y Z : SSet.{u}}
    {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f₀ ≫ g₀) (f₁ ≫ g₀)) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g₀ g₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f₀ ≫ g₁) (f₁ ≫ g₁) :=
  (d.precomp f₀).symm ≪≫ e ≪≫ d.precomp f₁
/-- 移した比較の順方向射は、元の同じ実ホモトピーを次の後続関手で写した辺の類。 -/
lemma functorIsoPostcompConjugate_hom {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (H : SSet.Homotopy f₀ f₁) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f₀ ≫ g₀) (f₁ ≫ g₀))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g₀ g₁)
    (he : e.hom = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₀))) :
    (functorIsoPostcompConjugate e d).hom = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₁)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopy_postcomp_iso_exchange H d
  rw [← he] at h
  simp only [functorIsoPostcompConjugate, Iso.trans_hom, Iso.symm_hom]
  rw [h, Iso.inv_hom_id_assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
