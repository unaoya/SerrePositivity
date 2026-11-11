module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerExchange
/-!
概要：二つの元の全単体ホモトピーの前後合成は、同じ全関手射の交換則を満たす。
方針：元の円柱の類を任意の関手変換の交換正方形へ代入する。
規約：いずれの生のホモトピーにも可逆性を仮定しない。使われ方：K-flat 変形円柱の二段交換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 二つの元の円柱の前後合成の順序は、同じ全関手射の正方形として交換できる。 -/
lemma homotopy_whisker_exchange {X Y Z : SSet.{u}} [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} (H : SSet.Homotopy f₀ f₁)
    {g₀ g₁ : Y ⟶ Z} (G : SSet.Homotopy g₀ g₁) :
    Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₀)) ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp G f₁)) =
    Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp G f₀)) ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₁)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy G))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
