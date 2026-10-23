module
public import SerrePositivity.InfinityCategories.F1B.TriangleBoundaryGluing
public import SerrePositivity.InfinityCategories.F1.Diagrams.CompositionTriangleSpace
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-! 三つの指定ホモトピーの全区間族を、関手単体集合の同じ三角形境界へ貼る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
variable {K X : SSet.{u}} {a b c : K ⟶ X}
  (l : SSet.Homotopy a b) (r : SSet.Homotopy b c) (d : SSet.Homotopy a c)

def dgGluingHomotopyTriangleBoundary : (boundary 2 : SSet.{u}) ⟶ (ihom K).obj X :=
  triangleBoundaryDiagram
    (composableEdgeHorn (functorEdgeOfSimplicialHomotopy l) (functorEdgeOfSimplicialHomotopy r))
    (SSet.yonedaEquiv.symm (functorEdgeOfSimplicialHomotopy d).edge) (by
      rw [composableEdgeHorn_first]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact (functorEdgeOfSimplicialHomotopy d).src_eq.trans
        (functorEdgeOfSimplicialHomotopy l).src_eq.symm) (by
      rw [composableEdgeHorn_last]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact (functorEdgeOfSimplicialHomotopy d).tgt_eq.trans
        (functorEdgeOfSimplicialHomotopy r).tgt_eq.symm)

lemma dgGluingHomotopyTriangleBoundary_zero :
    boundary.ι (0 : Fin 3) ≫ dgGluingHomotopyTriangleBoundary l r d = curry r.h := by
  rw [dgGluingHomotopyTriangleBoundary, triangleBoundaryDiagram_face_zero,
    composableEdgeHorn_last]
  exact Equiv.symm_apply_apply _ _

lemma dgGluingHomotopyTriangleBoundary_one :
    boundary.ι (1 : Fin 3) ≫ dgGluingHomotopyTriangleBoundary l r d = curry d.h := by
  rw [dgGluingHomotopyTriangleBoundary, triangleBoundaryDiagram_face_one]
  exact Equiv.symm_apply_apply _ _

lemma dgGluingHomotopyTriangleBoundary_two :
    boundary.ι (2 : Fin 3) ≫ dgGluingHomotopyTriangleBoundary l r d = curry l.h := by
  rw [dgGluingHomotopyTriangleBoundary, triangleBoundaryDiagram_face_two,
    composableEdgeHorn_first]
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.InfinityCategories
