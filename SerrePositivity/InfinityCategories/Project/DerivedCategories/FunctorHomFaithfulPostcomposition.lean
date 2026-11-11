module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
/-!
概要：充満忠実な実包含への後合成は、任意の全関手射の等式を反映する。
方針：全関手圏への後合成の充満忠実性をホモトピー圏で使う。
規約：可逆な射に限定しない。使われ方：K-flat 圏内の実 augmentation 正方形の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
/-- 充満忠実な実包含への後合成は、全関手圏の非可逆な射の等式も反映する。 -/
lemma functorHom_postcomp_injective_of_isFullyFaithful {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {q : X ⟶ Y} (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q)
    {f g : K ⟶ X} :
    Function.Injective (fun e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g =>
      (SSet.mapHomotopyCategory ((ihom K).map q)).map e) := by
  intro a b h
  apply (hq.postcompose K).toHoFullyFaithful.map_injective
  simpa only using! h
/-- 指定同型と元の二円柱の正方形は、充満忠実な包含後の同じ正方形から反映できる。 -/
lemma functorIso_homotopy_square_of_postcomp {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (q : X ⟶ Y) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q)
    {f g h : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (H : SSet.Homotopy g h) (G : SSet.Homotopy f h)
    (he : (e.postcomp q).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q)) =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp G q))) :
    e.hom ≫ Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy G) := by
  apply functorHom_postcomp_injective_of_isFullyFaithful hq
  simpa only [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom] using! he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
