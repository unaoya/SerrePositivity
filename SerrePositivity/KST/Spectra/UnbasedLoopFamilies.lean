module

public import SerrePositivity.KST.Spectra.UnbasedMapVertices
public import SerrePositivity.KST.Spectra.MappingFiberPaths

/-!
概要：loop 値の通常の射から、写像空間の実際の基点付き辺を構成する。
方針：loop の path 表示を転置し、両端が定数写像となることを使う。
規約：区間の向きを反転しない。
使われ方：Goerss–Jardine VIII §1。path 延長の底の基本群入力を固定する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- loop 値の射が定める、通常の写像空間の基点付き辺。 -/
def loopFamilySimplex {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) : (obj A Y).right.PtSimplex 1 (obj A Y).basepoint where
  map := pathFamilyEdge Y (f ≫ (PointedMapping.loopToPath Y).right)
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    fin_cases j
    · change stdSimplex.δ (0 : Fin 2) ≫
        pathFamilyEdge Y (f ≫ (PointedMapping.loopToPath Y).right) = _
      rw [pathFamilyEdge_face_zero Y _, Category.assoc, PointedMapping.loopToPath_endpoint,
        comp_const, mapVertex_const, SSet.yonedaEquiv_symm_zero]
    · exact pathFamilyEdge_face_one Y _

/-- loop の辺の族は源への制限と可換。 -/
lemma loopFamilySimplex_pre {A B : SSet.{u}} (i : A ⟶ B)
    (Y : PointedSimplicialSet.{u}) (f : B ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (pre i Y).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pre i Y))
        (loopFamilySimplex Y f) = loopFamilySimplex Y (i ≫ f) := by
  ext : 1
  change pathFamilyEdge Y (f ≫ (PointedMapping.loopToPath Y).right) ≫ (pre i Y).right = _
  rw [pathFamilyEdge_pre]
  rfl

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
