module

public import SerrePositivity.KST.Spectra.PointedBasedPathComposition
public import SerrePositivity.KST.Spectra.FibrationDifferenceTriangleLift

/-!
概要：共通の始点を持つ二つの実区間から、同じ三角形を保つ終点の比較区間を作る。
方針：点つき内部 Hom の外二次元ホーンを充填する。
規約：元の二辺を全体で固定。使われ方：二つの厳密化の段ごとの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 共通始点の二辺と、終点の比較辺および実三角形を保持する。 -/
structure BasedPathDifference {T E : PointedSimplicialSet.{u}} {f g h : T ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) f h) where
  path : VerticalPath (PointedObject.toPoint E) g h
  triangle : SSet.Edge.CompStruct P.edge path.edge Q.edge

/-- 元の二辺を固定する外ホーン充填から、同じ実三角形を持つ比較区間を選ぶ。 -/
def BasedPathDifference.choose {T E : PointedSimplicialSet.{u}} [KanComplex E.right]
    {f g h : T ⟶ E} (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) f h) : BasedPathDifference P Q := by
  let homKan : KanComplex (PointedObject.basedHom T E).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let p := Limits.terminal.from (PointedObject.basedHom T E).right
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  let hex := exists_difference_triangle_lift p hp P.edge Q.edge
    (Limits.terminal.from (Δ[2] : SSet.{u})) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  refine ⟨basedPathOfEdge hex.choose, ?_⟩
  rw [basedPathOfEdge_edge]
  exact hex.choose_spec.choose

/-- 同じ実区間の懸垂・後合成は、対応する全 Hom の一つの射への後合成。 -/
lemma VerticalPath.suspension_basedPost_path {T E V : PointedSimplicialSet.{u}}
    {f g : T ⟶ E} (P : VerticalPath (PointedObject.toPoint E) f g)
    (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension E ⟶ V) :
    (P.suspension.forgetProjection.basedPost s).path =
      P.path ≫ (suspensionHom T E ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension T)).map s).right := by
  change (P.path ≫ (suspensionHom T E).right) ≫
    ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension T)).map s).right = _
  rw [Under.comp_right, Category.assoc]

variable {T E : PointedSimplicialSet.{u}} {f g h : T ⟶ E}
  {P : VerticalPath (PointedObject.toPoint E) f g}
  {Q : VerticalPath (PointedObject.toPoint E) f h} (C : BasedPathDifference P Q)

/-- 比較三角形の第一辺は、元の第一の実区間そのもの。 -/
lemma BasedPathDifference.triangle_two :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex = P.path := by
  rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 比較三角形の対角辺は、元の第二の実区間そのもの。 -/
lemma BasedPathDifference.triangle_one :
    stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex = Q.path := by
  rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 比較三角形の第二辺は、同じ外ホーン充填で選んだ終点比較区間。 -/
lemma BasedPathDifference.triangle_zero :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex = C.path.path := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.KST.Spectra.PointedMapping
