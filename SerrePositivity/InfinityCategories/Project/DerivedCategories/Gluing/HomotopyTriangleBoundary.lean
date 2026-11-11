module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.TriangleBoundaryGluing
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.CompositionTriangleSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! 三つの指定ホモトピーの全区間族を、関手単体集合の同じ三角形境界へ貼る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {a b c : K ⟶ X}
  (l : SSet.Homotopy a b) (r : SSet.Homotopy b c) (d : SSet.Homotopy a c)

def dgGluingHomotopyTriangleBoundary : (boundary 2 : SSet.{u}) ⟶ (ihom K).obj X :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d).edge) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_first]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d).src_eq.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l).src_eq.symm) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_last]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d).tgt_eq.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r).tgt_eq.symm)

lemma dgGluingHomotopyTriangleBoundary_zero :
    boundary.ι (0 : Fin 3) ≫ dgGluingHomotopyTriangleBoundary l r d = curry r.h := by
  rw [dgGluingHomotopyTriangleBoundary, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram_face_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_last]
  exact Equiv.symm_apply_apply _ _

lemma dgGluingHomotopyTriangleBoundary_one :
    boundary.ι (1 : Fin 3) ≫ dgGluingHomotopyTriangleBoundary l r d = curry d.h := by
  rw [dgGluingHomotopyTriangleBoundary, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram_face_one]
  exact Equiv.symm_apply_apply _ _

lemma dgGluingHomotopyTriangleBoundary_two :
    boundary.ι (2 : Fin 3) ≫ dgGluingHomotopyTriangleBoundary l r d = curry l.h := by
  rw [dgGluingHomotopyTriangleBoundary, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram_face_two,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_first]
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
