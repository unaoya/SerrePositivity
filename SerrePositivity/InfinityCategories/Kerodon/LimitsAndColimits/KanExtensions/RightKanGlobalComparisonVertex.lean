module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportComparisonVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomUniversal

/-!
概要：既存の指定右Kan延長の大域比較は、元の指定輸送錐の標準極限比較を成分に持つ。
方針：既存のkanRightKanExtensionIsoとhom_facを使い、錐の極限性も元のKan延長から証明する。
規約：HTT 4.3.2.15（双対）、Kerodon §7.3（Tag 02Y1）の既存比較の計算法則。
使われ方：S8 の固定された値比較と、元の全関手の大域比較との照合。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元の大域Kan比較の同じ成分は、元の指定余単位の任意の輸送錐の標準極限比較に一致する。 -/
lemma kanRightKanExtensionIso_transport_vertex
    {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (hα : IsRightKanExtension δ F₀ F α) (hβ : IsRightKanExtension δ F₀ G β)
    (c : C _⦋0⦌) (t : RightKanConeTransport δ F₀ F α c)
    (s : RightKanConeTransport δ F₀ G β c) :
    let ht := (isRightKanExtension_iff_forall_transport δ F₀ F α).mp hα c t
    let hs := (isRightKanExtension_iff_forall_transport δ F₀ G β).mp hβ c s
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D)) t.cone_vertex.symm) ≫
      (limitVertexIso t.cone s.cone ht hs).hom ≫
        eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D)) s.cone_vertex) =
      functorHomEvaluate (kanRightKanExtensionIso δ α β hα hβ).hom c := by
  exact rightKanTransport_comparison_vertex α β (kanRightKanExtensionIso δ α β hα hβ)
    (kanRightKanExtensionIso_hom_fac δ α β hα hβ) c t s
    ((isRightKanExtension_iff_forall_transport δ F₀ F α).mp hα c t)
    ((isRightKanExtension_iff_forall_transport δ F₀ G β).mp hβ c s)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
