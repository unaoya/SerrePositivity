module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.HomotopyPrecompInverse
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.HomotopyEndpointTransport

/-!
概要：元の逆代表を先に選んで前合成し、同じ raw な順方向円柱の指定端点へ表示変更する。
方針：円柱の両端の式から等式を取り、逆の射の類を Arrow で移す。
規約：path end の逆代表の選択順を保持。使われ方：共通 end の実際の逆円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B X : SSet.{u}} [KanComplex X] {f g : B ⟶ X}
  (H : SSet.Homotopy f g) (i : A ⟶ B) {f' g' : A ⟶ X} (K : SSet.Homotopy f' g')
  (hK : K.h = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i).h)

/-- 元の逆代表への前合成を、同じ raw な順方向円柱の両端で厳密に表示する。 -/
def homotopyPrecompInverseTransport : SSet.Homotopy g' f' :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H).symm) i)
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i).h₁.symm.trans
      ((congrArg (SSet.ι₁ ≫ ·) hK.symm).trans K.h₁))
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i).h₀.symm.trans
      ((congrArg (SSet.ι₀ ≫ ·) hK.symm).trans K.h₀))

/-- 端点の表示変更後も、元の逆代表を先に選んで前合成した同じ raw な円柱。 -/
lemma homotopyPrecompInverseTransport_raw :
    (homotopyPrecompInverseTransport H i K hK).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H).symm) i).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 同じ逆代表の類は、指定した順方向円柱の同型の逆である。 -/
lemma homotopyPrecompInverseTransport_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (homotopyPrecompInverseTransport H i K hK)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy K).inv := by
  have ha := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (homotopyPrecompInverseTransport H i K hK) _ (homotopyPrecompInverseTransport_raw H i K hK)
  have hb := congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyPrecompInverse_hom H i)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowIsoInverse_congr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy K)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i) K hK.symm)
  have h := ha.trans (hb.trans hc)
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
