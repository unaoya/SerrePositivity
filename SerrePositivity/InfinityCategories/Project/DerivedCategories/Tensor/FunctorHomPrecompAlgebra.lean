module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.ResolutionComparisons.DeformationHomNaturality
/-!
概要：任意の全関手射の前合成則と実ホモトピーとの交換を証明する。
方針：実関手空間の前合成写像と同じ正方形を使う。
規約：可逆性は不要。使われ方：変形降下比較の射に対する自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorHom_precomp_id {X Y : SSet.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    (SSet.mapHomotopyCategory ((pre (𝟙 X)).app Y)).map e = e := by
  have hf : SSet.mapHomotopyCategory ((pre (𝟙 X)).app Y) =
      𝟭 (SSet.HomotopyCategory ((ihom X).obj Y)) := by
    change (hoFunctor.map ((pre (𝟙 X)).app Y)).toFunctor = _
    rw [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id]
    rfl
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorMapHom_heq_of_functor_eq hf e)
lemma functorHom_precomp_precomp {A B X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (p : B ⟶ X) (q : A ⟶ B) :
    (SSet.mapHomotopyCategory ((pre q).app Y)).map
      ((SSet.mapHomotopyCategory ((pre p).app Y)).map e) =
    (SSet.mapHomotopyCategory ((pre (q ≫ p)).app Y)).map e := by
  have hn : (pre (q ≫ p)).app Y = (pre p).app Y ≫ (pre q).app Y := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    rfl
  have hh := congrArg (fun k => SSet.mapHomotopyCategory k) hn
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapHomotopyCategory_comp_eq] at hh
  exact (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorMapHom_heq_of_functor_eq hh e)).symm
lemma homotopy_postcomp_hom_exchange {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} (H : SSet.Homotopy f₀ f₁)
    {g₀ g₁ : Y ⟶ Z} (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g₀ g₁) :
    Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₀)) ≫
      (SSet.mapHomotopyCategory ((pre f₁).app Z)).map d =
    (SSet.mapHomotopyCategory ((pre f₀).app Z)).map d ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H g₁)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) d
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
