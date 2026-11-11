module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomGeneral
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-!
概要：可逆とは限らない実関手変換と、前後合成による交換則を証明する。
方針：元の二つの実辺の積の正方形を、全関手空間の合成へ写す。
規約：変換の可逆性を要求しない。使われ方：augmentation と raw factor の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 実ホモトピーと指定関手同型の交換は、元の全関手圏の変換の等式を与える。 -/
lemma homotopy_postcomp_iso_exchange {X Y Z : SSet.{u}} [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} (H : SSet.Homotopy f₀ f₁)
    {g₀ g₁ : Y ⟶ Z} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g₀ g₁) :
    Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₀)) ≫
      (d.precomp f₁).hom =
    (d.precomp f₀).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₁)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) d.hom
end SerrePositivity.InfinityCategories.Project.DerivedCategories
