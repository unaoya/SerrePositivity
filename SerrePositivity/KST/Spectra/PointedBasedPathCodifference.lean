module

public import SerrePositivity.KST.Spectra.FibrationCodifferenceTriangleLift
public import SerrePositivity.KST.Spectra.PointedBasedPathComposition

/-!
概要：同じ終点へ至る二つの元の実区間を、実三角形を保持した始点比較へ移す。
方針：同じ内部 Hom の外二次元ホーンを充填し、二つの指定辺を保持する。
規約：区間を端点の成分類へ弱めない。使われ方：実評価側と Kan 随伴側の段比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ終点の元の二辺と、始点比較の辺および実三角形を保持する。 -/
structure BasedPathCodifference {T E : PointedSimplicialSet.{u}} {f g h : T ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f h)
    (Q : VerticalPath (PointedObject.toPoint E) g h) where
  path : VerticalPath (PointedObject.toPoint E) f g
  triangle : SSet.Edge.CompStruct path.edge Q.edge P.edge

/-- 元の二辺を固定する外ホーン充填から、同じ実三角形を持つ始点比較を選ぶ。 -/
def BasedPathCodifference.choose {T E : PointedSimplicialSet.{u}} [KanComplex E.right]
    {f g h : T ⟶ E} (P : VerticalPath (PointedObject.toPoint E) f h)
    (Q : VerticalPath (PointedObject.toPoint E) g h) : BasedPathCodifference P Q := by
  let homKan : KanComplex (PointedObject.basedHom T E).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let p := Limits.terminal.from (PointedObject.basedHom T E).right
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  let hex := exists_codifference_triangle_lift p hp P.edge Q.edge
    (Limits.terminal.from (Δ[2] : SSet.{u})) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  refine ⟨basedPathOfEdge hex.choose, ?_⟩
  rw [basedPathOfEdge_edge]
  exact hex.choose_spec.choose

variable {T E : PointedSimplicialSet.{u}} {f g h : T ⟶ E}
  {P : VerticalPath (PointedObject.toPoint E) f h}
  {Q : VerticalPath (PointedObject.toPoint E) g h} (C : BasedPathCodifference P Q)

/-- 実三角形の第一辺は、同じ外ホーン充填で選んだ始点比較。 -/
lemma BasedPathCodifference.triangle_two :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex = C.path.path := by
  rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 実三角形の対角辺は、元の第一の実区間そのもの。 -/
lemma BasedPathCodifference.triangle_one :
    stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex = P.path := by
  rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 実三角形の第二辺は、元の第二の実区間そのもの。 -/
lemma BasedPathCodifference.triangle_zero :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex = Q.path := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.KST.Spectra.PointedMapping
