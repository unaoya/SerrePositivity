module

public import SerrePositivity.KST.Spectra.FibrationEdgeComposition
public import SerrePositivity.KST.Spectra.PointedBasedPathComposition

/-!
概要：指定非零境界区間を保つ区間と境界固定区間を、その同じ境界区間を保って合成する。
方針：制限 fibration の上で退化合成三角形を指定し、二辺を固定した内ホーンを充填する。
規約：区間全体と合成三角形の射影を厳密に保持。使われ方：相対厳密化後の実ホモトピー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 境界の指定区間と退化三角形を変えずに、元の二つの比較区間を合成する。 -/
lemma exists_based_composite_over_restriction {A B E : PointedSimplicialSet.{u}}
    [KanComplex E.right] (j : B ⟶ A) [Mono j.right]
    {f g h : A ⟶ E} {a b : B ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) g h)
    (R : VerticalPath (PointedObject.toPoint E) a b)
    (hP : P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = R.path)
    (hQ : Q.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = SSet.const (familyVertex b)) :
    ∃ C : BasedPathComposite P Q,
      C.path.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = R.path ∧
      SSet.yonedaEquiv.symm C.triangle.simplex ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right =
        SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId R.edge).simplex := by
  have hp : SSet.modelCategoryQuillen.J.rlp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration j E)
  have hP' : SSet.yonedaEquiv.symm P.edge.edge ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right =
      SSet.yonedaEquiv.symm R.edge.edge := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv P.path) ≫ _ =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv R.path)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hP
  have hQ' : SSet.yonedaEquiv.symm Q.edge.edge ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right =
      SSet.const (familyVertex b) := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv Q.path) ≫ _ = _
    rw [Equiv.symm_apply_apply]
    exact hQ
  obtain ⟨e, t, he, ht⟩ := exists_edge_composite_over_path (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right hp
    P.edge Q.edge R.edge hP' hQ'
  have he' : e.edge = (basedPathOfEdge e).edge.edge :=
    (congrArg SSet.Edge.edge (basedPathOfEdge_edge e)).symm
  let C : BasedPathComposite P Q := {
    path := basedPathOfEdge e
    triangle := {
      simplex := t.simplex
      d₂ := t.d₂
      d₀ := t.d₀
      d₁ := t.d₁.trans he' } }
  refine ⟨C, ?_, ht⟩
  change SSet.yonedaEquiv.symm e.edge ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = R.path
  change _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv R.path) at he
  rw [Equiv.symm_apply_apply] at he
  exact he

end SerrePositivity.KST.Spectra.PointedMapping
