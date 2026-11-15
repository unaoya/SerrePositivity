module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConePostcomposeComponent
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：通常の錐の後合成の全変換は、底で元の指定自然変換そのものになる。
方針：既存のホモトピーの底の全写像の式を、同じ係数の後合成へ移す。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の指定右 Kan 射との照合。
規約：端点の表示は Arrow で相殺し、変換の代表を選び直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ係数で写した全錐の変換を底へ制限すると、元の指定自然変換の像になる。 -/
lemma nerveConePostcomposeHom_boundary {I C : Type u}
    [Category.{u} I] [Category.{u} C] {F G : I ⥤ C} (c : Cone F) (η : F ⟶ G)
    {X : SSet.{u}} (U : nerve C ⟶ X) :
    kanFunctorHomCongr (mapJoinCone U (nerveCone c)).property
      (mapJoinCone U (nerveCone ((Cone.postcompose η).obj c))).property
      ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) (nerve I))).app X)).toFunctor.map
        (nerveConePostcomposeHom c η U)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (nerveNatTransHomotopy η) U)) := by
  apply Arrow.mk_injective
  rw [kanFunctorHomCongr_arrow]
  unfold nerveConePostcomposeHom
  rw [← functorHomotopyPrecomp_hom]
  apply functorHomotopy_hom_arrow_of_h_eq
  change (joinInr (Δ[0] : SSet.{u}) (nerve I) ▷ (Δ[1] : SSet.{u})) ≫
    (nerveConePostcomposeHomotopy c η).h ≫ U = (nerveNatTransHomotopy η).h ≫ U
  rw [← Category.assoc, nerveConePostcomposeHomotopy_diagram]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
