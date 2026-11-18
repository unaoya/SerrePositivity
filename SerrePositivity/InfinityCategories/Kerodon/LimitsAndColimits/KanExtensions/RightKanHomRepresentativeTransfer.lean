module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanFunctorIsoTransfer
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：同じ指定余単位の類の既存ホモトピー代表へ、元の右Kan条件を移す。
方針：代表の辺の類の回収式と、同じ指定関手同型による既存の係数移送を使う。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の代表移送の法則。
使われ方：S8 の大域Hom比較から実際の指定右Kan輸送へ接続する。Hom普遍性を仮定にしない。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 指定余単位の同じ類の代表に、同じ全関手比較を保って実際の右Kan条件を移す。 -/
lemma isRightKanExtension_homRepresentative_of_compatible_functorIso
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (b : FunctorHom (δ ≫ G) F₀)
    (η : FunctorIso F G)
    (hη : rightKanHomMap δ b F η.hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
    (hα : IsRightKanExtension δ F₀ F α) :
    IsRightKanExtension δ F₀ G (functorHomHomotopy b) := by
  apply isRightKanExtension_of_compatible_functorIso α (functorHomHomotopy b) η _ hα
  simpa only [functorHomHomotopy_hom] using hη

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
