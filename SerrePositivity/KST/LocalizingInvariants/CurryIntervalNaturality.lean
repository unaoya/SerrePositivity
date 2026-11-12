module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CurryIntervalNaturality

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.CurryHomotopy
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：元の正方形の全ホモトピーから、辺の関手圏の四辺の可換式を導く。
方針：curry 後の自然性を、同じ切片と元の水平ホモトピーの類へ戻す。
規約：頂点成分を h X の射に弱めない。使われ方：三角形の相対 prism の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CurryInterval

variable {A X : SSet.{u}}

lemma commutation [Quasicategory X] {F G : A ⊗ Δ[1] ⟶ X} (H : SSet.Homotopy F G) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal F)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice H (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice H (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal G)) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.naturality H
    (SSet.Edge.ofTruncated (X := (Δ[1] : SSet.{u})) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)
  have hl := arrow_mk_comp_congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal_arrow F)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.component_arrow H (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  have hr := arrow_mk_comp_congr
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.component_arrow H (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal_arrow G)
  apply Arrow.mk_injective
  exact hl.symm.trans ((congrArg Arrow.mk hn).trans hr)

end SerrePositivity.KST.LocalizingInvariants.CurryInterval
